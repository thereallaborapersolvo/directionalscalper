# multi_bot_aio.py
import sys
import os
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from concurrent.futures import Future
import threading
from threading import Thread
import random
import colorama
from colorama import Fore, Back, Style, init
from pathlib import Path

# Determine the project directory and adjust the system path
project_dir = str(Path(__file__).resolve().parent)
print("Project directory:", project_dir)
sys.path.insert(0, project_dir)

import inspect
import traceback

import inquirer
from rich.live import Live
import argparse
from config import load_config, Config, VERSION
from api.manager import Manager

from directionalscalper.core.exchanges import *

import directionalscalper.core.strategies.bybit.gridbased as gridbased
import directionalscalper.core.strategies.bybit.hedging as bybit_hedging
from directionalscalper.core.strategies.binance import *
from directionalscalper.core.strategies.huobi import *

from live_table_manager import LiveTableManager  # CHANGED
from directionalscalper.core.strategies.base_strategy import BaseStrategy, shared_symbols_data  # ADDED

from directionalscalper.core.strategies.logger import Logger

from rate_limit import RateLimit

from collections import deque

# Initialize rate limiters
general_rate_limiter = RateLimit(50, 1)
order_rate_limiter = RateLimit(5, 1) 

# Initialize threading locks and data structures
thread_management_lock = threading.Lock()
thread_to_symbol = {}
thread_to_symbol_lock = threading.Lock()

# **New Lock for Synchronizing Active Symbol Counts**
active_symbols_lock = threading.Lock()

# **New Lock for Thread Info Logging**
thread_info_lock = threading.Lock()

active_symbols = set()
# active_threads = []
long_threads = {}
short_threads = {}
active_long_symbols = set()
active_short_symbols = set()
unique_active_symbols = set()

threads = {}  # Threads for each symbol
thread_start_time = {}  # Dictionary to track the start time for each symbol's thread
symbol_last_started_time = {}

extra_symbols = set()  # To track symbols opened past the limit
under_review_symbols = set()

latest_rotator_symbols = set()
last_rotator_update_time = time.time()
tried_symbols = set()

rotator_symbols_cache = {
    'timestamp': 0,
    'symbols': set()
}
CACHE_DURATION = 50  # Cache duration in seconds

# Initialize logger
logging = Logger(logger_name="MultiBot", filename="MultiBot.log", stream=True)

# Initialize colorama
colorama.init()

# Global variable to track the last spawn time for each symbol
symbol_last_spawn_time = {}  # CHANGED: Moved to global scope

def can_spawn_thread(symbol):
    """
    Checks if a thread can be spawned for a symbol based on cooldown logic.
    """
    COOLDOWN_PERIOD = 60  # Cooldown period in seconds
    current_time = time.time()
    last_spawn_time = symbol_last_spawn_time.get(symbol, 0)
    if current_time - last_spawn_time >= COOLDOWN_PERIOD:
        symbol_last_spawn_time[symbol] = current_time
        return True
    logging.info(f"Cooldown active for symbol {symbol}. Skipping thread spawn.")
    return False  # CHANGED: Return False when cooldown is active

def print_cool_trading_info(symbol, exchange_name, strategy_name, account_name):
    ascii_art = r"""
    ____  _               _   _                   _  ____            _                
   |  _ \(_)_ __ ___  ___| |_(_) ___  _ __   __ _| |/ ___|  ___ __ _| |_ __   ___ _ __ 
   | | | | | '__/ _ \/ __| __| |/ _ \| '_ \ / _ | |\___ \ / __/ _ | | '_ \ / _ \ '__|
   | |_| | | | |  __/ (__| |_| | (_) | | | | (_| | | ___) | (_| (_| | | |_) |  __/ |   
   |____/|_|_|  \___|\___|___|_|\___/|_| |_|\__,_|_||____/ \___\__,_|_| .__/ \___|_|   
                                                                       |_|              
    ╔═══════════════════════════════════════════════════════════════════════════╗
    ║          Created by Tyler Simpson and contributors at QVL                 ║
    ╚═══════════════════════════════════════════════════════════════════════════╝
    """
    print(Fore.CYAN + ascii_art)
    print(Style.BRIGHT + Fore.YELLOW + "DirectionalScalper is trading..")
    print(Fore.GREEN + f"Trading symbol: {symbol}")
    print(Fore.MAGENTA + f"Exchange name: {exchange_name}")
    print(Fore.BLUE + f"Strategy name: {strategy_name}")
    print(Fore.RED + f"Account name: {account_name}")
    print(Style.RESET_ALL)

def standardize_symbol(symbol):
    return symbol.replace('/', '').split(':')[0]

def get_available_strategies():
    return [
        'qsgridob'
        # Add other strategies here as needed
    ]

def choose_strategy():
    questions = [
        inquirer.List('strategy',
                      message='Which strategy would you like to run?',
                      choices=get_available_strategies())
    ]
    answers = inquirer.prompt(questions)
    return answers['strategy']

def get_available_exchanges():
    return ['bybit', 'hyperliquid']

def ask_for_missing_arguments(args):
    questions = []
    if not args.exchange:
        questions.append(inquirer.List('exchange', message="Which exchange do you want to use?", choices=get_available_exchanges()))
    if not args.strategy:
        questions.append(inquirer.List('strategy', message="Which strategy do you want to use?", choices=get_available_strategies()))
    if not args.account_name:
        questions.append(inquirer.Text('account_name', message="Please enter the name of the account:"))

    if questions:
        answers = inquirer.prompt(questions)
        args.exchange = args.exchange or answers.get('exchange')
        args.strategy = args.strategy or answers.get('strategy')
        args.account_name = args.account_name or answers.get('account_name')

    return args

class DirectionalMarketMaker:
    def __init__(self, config: Config, exchange_name: str, account_name: str):
        self.config = config
        self.exchange_name = exchange_name
        self.account_name = account_name
        self.entry_signal_type = config.bot.linear_grid.get('entry_signal_type', 'lorentzian')  # Default to lorentzian

        # Retrieve the specific exchange configuration
        exchange_config = next((exch for exch in config.exchanges if exch.name == exchange_name and exch.account_name == account_name), None)
        
        if not exchange_config:
            raise ValueError(f"Exchange {exchange_name} with account {account_name} not found in the configuration file.")

        api_key = exchange_config.api_key
        secret_key = exchange_config.api_secret
        passphrase = getattr(exchange_config, 'passphrase', None)  # Use getattr to get passphrase if it exists

        exchange_classes = {
            'bybit': BybitExchange,
            'bybit_spot': BybitExchange,
            'hyperliquid': HyperLiquidExchange,
            'huobi': HuobiExchange,
            'bitget': BitgetExchange,
            'binance': BinanceExchange,
            'mexc': MexcExchange,
            'lbank': LBankExchange,
            'blofin': BlofinExchange
        }

        exchange_class = exchange_classes.get(exchange_name.lower(), Exchange)

        # Initialize the exchange based on whether a passphrase is required
        if exchange_name.lower() in ['bybit', 'binance']:  # Add other exchanges here that do not require a passphrase
            self.exchange = exchange_class(api_key, secret_key)
        elif exchange_name.lower() == 'bybit_spot':
            self.exchange = exchange_class(api_key, secret_key, 'spot')
        else:
            self.exchange = exchange_class(api_key, secret_key, passphrase)
        
        self.manager = None  # Initialize to None; will be set externally

    def run_strategy(
        self,
        symbol,
        strategy_name,
        config,
        account_name,
        symbols_allowed_long,
        symbols_allowed_short,
        symbols_to_trade=None,
        rotator_symbols_standardized=None,
        mfirsi_signal=None,
        action=None,
        thread_completed=None  # New parameter
    ):
        logging.info(f"Received rotator symbols in run_strategy ({strategy_name}) for {symbol}: {rotator_symbols_standardized}")
        
        # Retrieve symbols_allowed_long and symbols_allowed_short from config
        exchange_config = next(
            (exch for exch in config.exchanges if exch.name == self.exchange_name and exch.account_name == account_name),
            None
        )
        if exchange_config:
            symbols_allowed_long_config = exchange_config.symbols_allowed_long
            symbols_allowed_short_config = exchange_config.symbols_allowed_short
        else:
            symbols_allowed_long_config = 1
            symbols_allowed_short_config = 1
            logging.warning(
                f"Exchange configuration not found for exchange: {self.exchange_name} and account: {account_name}. "
                f"Using default limits."
            )
        
        logging.info(
            f"Matched exchange: {self.exchange_name}, account: {account_name}. "
            f"symbols_allowed_long: {symbols_allowed_long_config}, symbols_allowed_short: {symbols_allowed_short_config}"
        )
        
        if symbols_to_trade:
            logging.info(f"Calling run method with symbols: {symbols_to_trade}")
            try:
                print_cool_trading_info(symbol, self.exchange_name, strategy_name, account_name)
                logging.info(f"Printed trading info for {symbol}")
            except Exception as e:
                logging.error(f"Error in printing info: {e}")

        # Define available strategy classes
        strategy_classes = {
            'qstrendobdynamictp': gridbased.BybitQuickScalpTrendDynamicTP,
            'qsgridob': gridbased.LinearGridBaseFutures
        }

        strategy_class = strategy_classes.get(strategy_name.lower())
        if strategy_class:
            # Initialize the strategy with appropriate parameters
            strategy = strategy_class(
                self.exchange,
                self.manager,
                config.bot,
                symbols_allowed_long_config,
                symbols_allowed_short_config
            )
            try:
                logging.info(f"[run_strategy] Running strategy for symbol {symbol} with action {action}")
                if action in ["manage_long", "long"]:
                    future_long = Future()
                    thread = Thread(
                        target=self.run_with_future,
                        args=(
                            strategy,
                            symbol,
                            rotator_symbols_standardized,
                            mfirsi_signal,
                            "long",
                            future_long,
                            thread_completed
                        )
                    )
                    thread.name = f"run_with_future({symbol}, long)"
                    thread.start()
                    return future_long
                elif action in ["manage_short", "short"]:
                    future_short = Future()
                    thread = Thread(
                        target=self.run_with_future,
                        args=(
                            strategy,
                            symbol,
                            rotator_symbols_standardized,
                            mfirsi_signal,
                            "short",
                            future_short,
                            thread_completed
                        )
                    )
                    thread.name = f"run_with_future({symbol}, short)"
                    thread.start()
                    return future_short
                else:
                    future = Future()
                    future.set_result(True)
                    return future
            except Exception as e:
                logging.error(f"Exception in run_strategy for {symbol}: {e}")
                future = Future()
                future.set_exception(e)
                return future
        else:
            logging.error(f"Strategy {strategy_name} not found.")
            future = Future()
            future.set_exception(ValueError(f"Strategy {strategy_name} not found."))
            return future


    def run_with_future(self, strategy, symbol, rotator_symbols_standardized, mfirsi_signal, action, future, thread_completed):
        try:
            logging.debug(f"[run_with_future] About to run strategy.run for {symbol}, action={action}")
            strategy.run(
                symbol,
                rotator_symbols_standardized=rotator_symbols_standardized,
                mfirsi_signal=mfirsi_signal,
                action=action,
                thread_completed=thread_completed
            )
            logging.debug(f"[run_with_future] Completed strategy.run for {symbol}, action={action}")
            future.set_result(True)
        except Exception as e:
            logging.error(f"Exception in run_with_future for {symbol}, action={action}: {e}")
            logging.error(traceback.format_exc())
            future.set_exception(e)

    def get_balance(self, quote, market_type=None, sub_type=None):
        if self.exchange_name == 'bitget':
            return self.exchange.get_balance_bitget(quote)
        elif self.exchange_name == 'bybit':
            return self.exchange.get_balance_bybit(quote)
        elif self.exchange_name == 'bybit_unified':
            return self.exchange.retry_api_call(self.exchange.get_balance_bybit(quote))
        elif self.exchange_name == 'mexc':
            return self.exchange.get_balance_mexc(quote, market_type='swap')
        elif self.exchange_name == 'huobi':
            print("Huobi starting..")
        elif self.exchange_name == 'okx':
            print(f"Unsupported for now")
        elif self.exchange_name == 'binance':
            return self.exchange.get_balance_binance(quote)
        elif self.exchange_name == 'phemex':
            print(f"Unsupported for now")

    def create_order(self, symbol, order_type, side, amount, price=None):
        return self.exchange.create_order(symbol, order_type, side, amount, price)

    def get_symbols(self):
        with general_rate_limiter:
            return self.exchange._get_symbols()

    def format_symbol_bybit(self, symbol):
        return f"{symbol[:3]}/{symbol[3:]}:USDT"

    def is_valid_symbol_bybit(self, symbol):
        valid_symbols = self.get_symbols()
        
        # Check for SYMBOL/USDT:USDT format
        if f"{symbol[:3]}/{symbol[3:]}:USDT" in valid_symbols:
            return True
        
        # Check for SYMBOL/USD:SYMBOL format
        if f"{symbol[:3]}/USD:{symbol[:3]}" in valid_symbols:
            return True
        
        # Check for SYMBOL/USDC:USDC format
        if f"{symbol}/USDC:USDC" in valid_symbols:
            return True
        
        # Check for SYMBOL/USDC:USDC-YYMMDD format
        for valid_symbol in valid_symbols:
            if valid_symbol.startswith(f"{symbol}/USDC:USDC-"):
                return True
        
        # Check for SYMBOL/USDC:USDC-YYMMDD-STRIKE-C/P format
        for valid_symbol in valid_symbols:
            if valid_symbol.startswith(f"{symbol}/USDC:USDC-") and valid_symbol.endswith(("-C", "-P")):
                return True
        
        logging.info(f"Invalid symbol type for some reason according to bybit but is probably valid symbol: {symbol}")
        return True

    def fetch_open_orders(self, symbol):
        with general_rate_limiter:
            return self.exchange.retry_api_call(self.exchange.get_open_orders, symbol)

    def get_signal(self, symbol):
        logging.info(f"Generating signal for symbol: {symbol} using entry_signal_type: {self.entry_signal_type}")
        if self.entry_signal_type == 'mfirsi_signal':
            logging.info(f"Using mfirsi signals for symbol {symbol}")
            signal = self.get_mfirsi_signal(symbol)
        elif self.entry_signal_type == 'lorentzian':
            logging.info(f"Using lorentzian signals for symbol {symbol}")
            signal = self.generate_l_signals(symbol)
        else:
            raise ValueError(f"Unknown entry signal type: {self.entry_signal_type}")

        logging.info(f"Generated signal for {symbol}: {signal}")
        if signal == "neutral":
            logging.info(f"Skipping processing for {symbol} due to neutral signal.")
            return "neutral"  # Return a specific flag for neutral signals
        return signal

    def generate_l_signals(self, symbol):
        with general_rate_limiter:
            return self.exchange.generate_l_signals(symbol)

    def get_mfirsi_signal(self, symbol):
        # Retrieve the MFI/RSI signal
        with general_rate_limiter:
            return self.exchange.get_mfirsi_ema_secondary_ema(symbol, limit=100, lookback=1, ema_period=5, secondary_ema_period=3)

# **Helper Functions with Updated Signatures and Synchronization**

def is_long_position(symbol, manager, exchange_name):
    pos_data = getattr(manager.exchange, f"get_all_open_positions_{exchange_name.lower()}")()
    # CHANGED: Access 'side' correctly
    is_long = any(standardize_symbol(pos['symbol']) == symbol and pos['side'].lower() == 'long' for pos in pos_data)
    logging.debug(f"Checked if {symbol} is a long position: {is_long}")
    return is_long

def is_short_position(symbol, manager, exchange_name):
    pos_data = getattr(manager.exchange, f"get_all_open_positions_{exchange_name.lower()}")()
    # CHANGED: Access 'side' correctly
    is_short = any(standardize_symbol(pos['symbol']) == symbol and pos['side'].lower() == 'short' for pos in pos_data)
    logging.debug(f"Checked if {symbol} is a short position: {is_short}")
    return is_short

def update_active_symbols(open_position_symbols, manager, exchange_name):
    global active_symbols, active_long_symbols, active_short_symbols, unique_active_symbols
    with active_symbols_lock:
        active_symbols = open_position_symbols
        active_long_symbols = {symbol for symbol in open_position_symbols if is_long_position(symbol, manager, exchange_name)}
        active_short_symbols = {symbol for symbol in open_position_symbols if is_short_position(symbol, manager, exchange_name)}
        unique_active_symbols = active_long_symbols.union(active_short_symbols)
        logging.info(f"Updated active symbols ({len(active_symbols)}): {active_symbols}")
        logging.info(f"Updated active long symbols ({len(active_long_symbols)}): {active_long_symbols}")
        logging.info(f"Updated active short symbols ({len(active_short_symbols)}): {active_short_symbols}")
        logging.info(f"Updated unique active symbols ({len(unique_active_symbols)}): {unique_active_symbols}")

def sync_positions_to_shared_data(open_positions):
    """
    Synchronize open positions to the shared_symbols_data dictionary for real-time updates in table manager.
    """
    with BaseStrategy.symbol_management_lock:
        logging.debug(f"Syncing {len(open_positions)} open positions to shared_symbols_data.")
        for pos in open_positions:
            sym = standardize_symbol(pos['symbol'])
            side = pos['side'].lower()
            
            # Access 'size' from 'info' dictionary
            qty = pos['info'].get('size', 0)  # Default to 0 if 'size' is not available
            
            # Access 'entryPrice' and 'unrealisedPnl' from 'info' dictionary
            entry_price = pos['info'].get('entryPrice', 0)  # Default to 0 if 'entryPrice' is missing
            upnl = pos['info'].get('unrealisedPnl', 0)      # Default to 0 if 'unrealisedPnl' is missing
            
            logging.debug(f"Processing position: Symbol={sym}, Side={side}, Qty={qty}, Entry Price={entry_price}, Unrealised PnL={upnl}")
            
            if 'size' not in pos['info']:
                logging.warning(f"Missing 'size' in position data: {pos}")  # ADDED

            if sym not in shared_symbols_data:
                shared_symbols_data[sym] = {}

            shared_symbols_data[sym]['symbol'] = sym

            # If there's a long side
            if side == 'long':
                shared_symbols_data[sym]['long_pos_qty'] = qty
                shared_symbols_data[sym]['long_pos_price'] = entry_price
                shared_symbols_data[sym]['long_upnl'] = round(float(upnl), 2)
                # Ensure short fields exist with default values
                shared_symbols_data[sym].setdefault('short_pos_qty', 0)
                shared_symbols_data[sym].setdefault('short_pos_price', 0)
                shared_symbols_data[sym].setdefault('short_upnl', 0.0)
            # If there's a short side
            elif side == 'short':
                shared_symbols_data[sym]['short_pos_qty'] = qty
                shared_symbols_data[sym]['short_pos_price'] = entry_price
                shared_symbols_data[sym]['short_upnl'] = round(float(upnl), 2)
                # Ensure long fields exist with default values
                shared_symbols_data[sym].setdefault('long_pos_qty', 0)
                shared_symbols_data[sym].setdefault('long_pos_price', 0)
                shared_symbols_data[sym].setdefault('long_upnl', 0.0)
            else:
                logging.warning(f"Unknown position side '{side}' for symbol {sym}. Skipping.")
    
    # After synchronization, log the entire shared_symbols_data
    logging.debug(f"After synchronization, shared_symbols_data contains {len(shared_symbols_data)} symbols.")


BALANCE_REFRESH_INTERVAL = 600  # in seconds

orders_canceled = False

def run_bot(symbol, args, market_maker, manager, account_name, symbols_allowed_long, symbols_allowed_short, rotator_symbols_standardized, thread_completed, mfirsi_signal, action):
    global orders_canceled, unique_active_symbols, active_long_symbols, active_short_symbols
    logging.info(f"Thread started for symbol: {symbol}, action: {action}")
    current_thread = threading.current_thread()
    try:
        logging.debug("Entering run_bot function.")
        
        # Load configuration
        if not args.config.startswith('configs/'):
            config_file_path = Path('configs/' + args.config)
        else:
            config_file_path = Path(args.config)

        logging.info(f"Loading config from: {config_file_path}")
        account_file_path = Path('configs/account.json')  # Define the account file path
        config = load_config(config_file_path, account_file_path)  # Pass both file paths to load_config
        logging.info("Configuration loaded successfully.")

        exchange_name = args.exchange
        strategy_name = args.strategy
        account_name = args.account_name

        logging.info(f"Trading symbol: {symbol}")
        logging.info(f"Exchange name: {exchange_name}")
        logging.info(f"Strategy name: {strategy_name}")
        logging.info(f"Account name: {account_name}")

        # Establish manager reference
        market_maker.manager = manager
        logging.debug("Manager reference set in market_maker.")

        # Fetch open positions
        def fetch_open_positions():
            with general_rate_limiter:
                return getattr(manager.exchange, f"get_all_open_positions_{exchange_name.lower()}")()

        open_position_data = fetch_open_positions()
        open_position_symbols = {standardize_symbol(pos['symbol']) for pos in open_position_data}
        logging.info(f"Open position symbols: {open_position_symbols}")

        current_long_positions = [standardize_symbol(pos['symbol']) for pos in open_position_data if pos['side'].lower() == 'long']
        current_short_positions = [standardize_symbol(pos['symbol']) for pos in open_position_data if pos['side'].lower() == 'short']

        logging.info(f"Current long positions: {current_long_positions}")
        logging.info(f"Current short positions: {current_short_positions}")

        with active_symbols_lock:
            is_open_position = symbol in open_position_symbols
            logging.debug(f"[run_bot] is_open_position={is_open_position}, symbol={symbol}, action={action}")
            
            # Adjusted Condition: Allow managing symbols that are already active
            can_manage_long = action == "manage_long" and (symbol in active_long_symbols or len(active_long_symbols) < symbols_allowed_long)
            can_manage_short = action == "manage_short" and (symbol in active_short_symbols or len(active_short_symbols) < symbols_allowed_short)
            
            if can_manage_long:
                active_symbols.add(symbol)
                active_long_symbols.add(symbol)
                unique_active_symbols.add(symbol)
                logging.info(f"Added symbol {symbol} to active_long_symbols.")
            elif can_manage_short:
                active_symbols.add(symbol)
                active_short_symbols.add(symbol)
                unique_active_symbols.add(symbol)
                logging.info(f"Added symbol {symbol} to active_short_symbols.")
            else:
                logging.info(f"Cannot manage symbol {symbol}. Limits reached.")
                return

        # Cancel all open orders if not already done
        try:
            if not orders_canceled and hasattr(market_maker.exchange, 'cancel_all_open_orders_bybit'):
                market_maker.exchange.cancel_all_open_orders_bybit()
                logging.info(f"Cleared all open orders on the exchange upon initialization.")
                orders_canceled = True
        except Exception as e:
            logging.error(f"Exception caught while cancelling orders: {e}")
            logging.debug(traceback.format_exc())

        logging.info(f"Rotator symbols in run_bot: {rotator_symbols_standardized}")
        logging.info(f"Latest rotator symbols in run_bot: {latest_rotator_symbols}")

        time.sleep(2)

        # Execute the strategy
        with general_rate_limiter:
            logging.info("Calling market_maker.get_signal.")
            signal = market_maker.get_signal(symbol)
            logging.info(f"Signal obtained for {symbol}: {signal}")
            symbols_to_trade = symbols_allowed_long if action == "manage_long" else symbols_allowed_short

            logging.info("Calling market_maker.run_strategy.")
            logging.debug(f"[run_bot] About to call run_strategy for {symbol}, action={action}, signal={signal}")
            future = market_maker.run_strategy(
                symbol,
                args.strategy,
                config,
                account_name,
                symbols_allowed_long,
                symbols_allowed_short,
                symbols_to_trade=symbols_to_trade,
                rotator_symbols_standardized=rotator_symbols_standardized,
                mfirsi_signal=signal,
                action=action,
                thread_completed=thread_completed  # Pass the event
            )

            logging.debug(f"[run_bot] run_strategy returned future={future} for {symbol}")

            # Wait for the strategy to complete
            result = future.result()  # This will block until the strategy completes
            logging.debug(f"[run_bot] Strategy completed for {symbol}, result={result}")

        while True:
            # Continuously monitor the position
            try:
                open_position_data_final = getattr(manager.exchange, f"get_all_open_positions_{exchange_name.lower()}")()
                open_symbol_set_final = {standardize_symbol(pos['symbol']) for pos in open_position_data_final}
                position_still_open = (symbol in open_symbol_set_final)

                if not position_still_open:
                    logging.info(f"Position closed for {symbol}. Cleaning up.")
                    break  # Exit the loop and allow thread to terminate

                # Optionally, perform periodic actions or updates here
                logging.debug(f"Position still open for {symbol}. Continuing management.")
                time.sleep(10)  # Adjust the sleep duration as needed

            except Exception as e:
                logging.warning(f"Could not fetch open positions in run_bot final check for {symbol}: {e}")
                position_still_open = False
                break  # Exit the loop to prevent indefinite waiting

    except Exception as e:
        logging.info(f"An error occurred in run_bot for symbol {symbol}: {e}")
        logging.info(traceback.format_exc())
    finally:
        with active_symbols_lock:
            try:
                # Fetch fresh positions from the exchange in the final block
                open_position_data_final = getattr(manager.exchange, f"get_all_open_positions_{args.exchange.lower()}")()
                open_symbol_set_final = {standardize_symbol(pos['symbol']) for pos in open_position_data_final}
                position_still_open = (symbol in open_symbol_set_final)
            except Exception as e:
                logging.warning(f"Could not fetch open positions in run_bot final check for {symbol}: {e}")
                position_still_open = False

            if not position_still_open:
                # If the exchange says the position is closed, remove from sets
                logging.info(f"Thread completed for {symbol}, exchange shows position closed. Removing from active sets.")
                active_symbols.discard(symbol)
                if action == "manage_long":
                    active_long_symbols.discard(symbol)
                elif action == "manage_short":
                    active_short_symbols.discard(symbol)
                unique_active_symbols.discard(symbol)
                logging.info(f"Removed {symbol} from active sets.")
            else:
                # Position is still open; the current thread continues managing it
                logging.info(f"Thread for {symbol} is continuing to manage an open position.")

        logging.info(f"Thread completed for symbol: {symbol}, action: {action}")
        thread_completed.set()


# New helper function for regular thread monitoring
def log_all_threads_status():
    logging.info("=== Current Active Threads ===")
    for symbol, (thread, completed) in long_threads.items():
        logging.info(f"LONG THREAD for {symbol}: ID={thread.ident}, Alive={thread.is_alive()}")
    for symbol, (thread, completed) in short_threads.items():
        logging.info(f"SHORT THREAD for {symbol}: ID={thread.ident}, Alive={thread.is_alive()}")
    logging.info("================================")


def bybit_auto_rotation(args, market_maker, manager, symbols_allowed_long, symbols_allowed_short):
    """
    Perform auto-rotation of symbols for Bybit exchange.
    """
    global latest_rotator_symbols, long_threads, short_threads, active_symbols, active_long_symbols, active_short_symbols, last_rotator_update_time, unique_active_symbols
    
    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Starting bybit_auto_rotation.")
    
    max_workers_signals = 1
    max_workers_trading = 1

    signal_executor = ThreadPoolExecutor(max_workers=max_workers_signals)
    trading_executor = ThreadPoolExecutor(max_workers=max_workers_trading)

    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Initialized signal executor with max workers: {max_workers_signals}")
    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Initialized trading executor with max workers: {max_workers_trading}")

    config_file_path = Path('configs/' + args.config) if not args.config.startswith('configs/') else Path(args.config)
    account_file_path = Path('configs/account.json')
    config = load_config(config_file_path, account_file_path)

    market_maker.manager = manager

    long_mode = config.bot.linear_grid['long_mode']
    short_mode = config.bot.linear_grid['short_mode']
    config_graceful_stop_long = config.bot.linear_grid.get('graceful_stop_long', False)
    config_graceful_stop_short = config.bot.linear_grid.get('graceful_stop_short', False)
    config_auto_graceful_stop = config.bot.linear_grid.get('auto_graceful_stop', False)
    target_coins_mode = config.bot.linear_grid.get('target_coins_mode', False)
    whitelist = set(config.bot.whitelist) if target_coins_mode else None

    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Target coins mode is {'enabled' if target_coins_mode else 'disabled'}")

    def fetch_open_positions():
        with general_rate_limiter:
            return getattr(manager.exchange, f"get_all_open_positions_{args.exchange.lower()}")()

    open_position_data = fetch_open_positions()
    current_long_positions = sum(1 for pos in open_position_data if pos['side'].lower() == 'long')
    current_short_positions = sum(1 for pos in open_position_data if pos['side'].lower() == 'short')

    graceful_stop_long = current_long_positions >= symbols_allowed_long or config_graceful_stop_long
    graceful_stop_short = current_short_positions >= symbols_allowed_short or config_graceful_stop_short

    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) current_long_positions: {current_long_positions}")
    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) current_short_positions: {current_short_positions}")

    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Long mode: {long_mode}")
    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Short mode: {short_mode}")
    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Initial Graceful stop long: {graceful_stop_long}")
    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Initial Graceful stop short: {graceful_stop_short}")
    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Auto graceful stop: {config_auto_graceful_stop}")
    
    # Thread cooldown management is handled globally

    def process_futures(futures):
        for future in as_completed(futures):
            try:
                future.result()
            except Exception as e:
                logging.error(f"Exception in thread: {e}")
                logging.debug(traceback.format_exc())

    processed_symbols = set()

    while True:
        try:
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Entering main loop for auto-rotation.")

            current_time = time.time()
            open_position_data = fetch_open_positions()

            # [ADDED] Synchronize shared_symbols_data for table updates
            sync_positions_to_shared_data(open_position_data)

            open_position_symbols = {standardize_symbol(pos['symbol']) for pos in open_position_data}
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Open position symbols: {open_position_symbols}")

            current_long_positions = sum(1 for pos in open_position_data if pos['side'].lower() == 'long')
            current_short_positions = sum(1 for pos in open_position_data if pos['side'].lower() == 'short')
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Current long positions: {current_long_positions}, Current short positions: {current_short_positions}")

            # **Synchronize Active Symbol Counts**
            with active_symbols_lock:
                active_symbols = open_position_symbols
                active_long_symbols = {symbol for symbol in open_position_symbols if is_long_position(symbol, manager, args.exchange)}
                active_short_symbols = {symbol for symbol in open_position_symbols if is_short_position(symbol, manager, args.exchange)}
                unique_active_symbols = active_long_symbols.union(active_short_symbols)
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated active symbols ({len(active_symbols)}): {active_symbols}")
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated active long symbols ({len(active_long_symbols)}): {active_long_symbols}")
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated active short symbols ({len(active_short_symbols)}): {active_short_symbols}")
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated unique active symbols ({len(unique_active_symbols)}): {unique_active_symbols}")

            if config_auto_graceful_stop:
                if (current_long_positions >= symbols_allowed_long or len(active_long_symbols) >= symbols_allowed_long) and not graceful_stop_long:
                    graceful_stop_long = True
                    logging.info(f"GS Auto Check: Automatically enabled graceful stop for long positions. Current long positions: {current_long_positions}, Active long symbols: {len(active_long_symbols)}")
                elif current_long_positions < symbols_allowed_long and len(active_long_symbols) < symbols_allowed_long and graceful_stop_long:
                    graceful_stop_long = config_graceful_stop_long
                    logging.info(f"GS Auto Check: Reverting to config value for graceful stop long. Current long positions: {current_long_positions}, Active long symbols: {len(active_long_symbols)}, Config value: {config_graceful_stop_long}")
                else:
                    logging.info(f"GS Auto Check: Current long positions: {current_long_positions}, Active long symbols: {len(active_long_symbols)}. Graceful stop long: {graceful_stop_long}")

                if (current_short_positions >= symbols_allowed_short or len(active_short_symbols) >= symbols_allowed_short) and not graceful_stop_short:
                    graceful_stop_short = True
                    logging.info(f"GS Auto Check: Automatically enabled graceful stop for short positions. Current short positions: {current_short_positions}, Active short symbols: {len(active_short_symbols)}")
                elif current_short_positions < symbols_allowed_short and len(active_short_symbols) < symbols_allowed_short and graceful_stop_short:
                    graceful_stop_short = config_graceful_stop_short
                    logging.info(f"GS Auto Check: Reverting to config value for graceful stop short. Current short positions: {current_short_positions}, Active short symbols: {len(active_short_symbols)}, Config value: {config_graceful_stop_short}")
                else:
                    logging.info(f"GS Auto Check: Current short positions: {current_short_positions}, Active short symbols: {len(active_short_symbols)}. Graceful stop short: {graceful_stop_short}")

            # **Always Enforce Per-Type Limits with Prioritization**
            manage_excess_threads(symbols_allowed_long, symbols_allowed_short, manager.symbols_allowed)

            # Refresh rotator symbols if needed
            if not latest_rotator_symbols or current_time - last_rotator_update_time >= 60:
                with general_rate_limiter:
                    latest_rotator_symbols = fetch_updated_symbols(args, manager, config, whitelist)  # CHANGED: Added 'config' parameter
                last_rotator_update_time = current_time
                processed_symbols.clear()
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Refreshed latest rotator symbols: {latest_rotator_symbols}")
            else:
                logging.debug(f"No refresh needed yet. Last update was at {last_rotator_update_time}, less than 60 seconds ago.")

            with thread_management_lock:
                open_position_futures = []
                signal_futures = []

                # Process signals for open positions
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno})  Process signals for open positions.")
                for symbol in open_position_symbols.copy():
                    has_open_long = symbol in active_long_symbols
                    has_open_short = symbol in active_short_symbols

                    with thread_info_lock:
                        # Updated references using (thread, event)
                        if symbol in long_threads:
                            thread, thread_completed = long_threads[symbol]
                            thread_ident = thread.ident
                            action_label = 'long'
                            log_message = (f"[[{symbol}]]: [Thread ID: {thread_ident}] In while true loop {symbol} for action {action_label}")
                            logging.info(log_message)
                        else:
                            logging.info(f"[[{symbol}]]: [Thread ID: N/A] Long thread not running.")

                        if symbol in short_threads:
                            thread, thread_completed = short_threads[symbol]
                            thread_ident = thread.ident
                            action_label = 'short'
                            log_message = (f"[[{symbol}]]: [Thread ID: {thread_ident}] In while true loop {symbol} for action {action_label}")
                            logging.info(log_message)
                        else:
                            logging.info(f"[[{symbol}]]: [Thread ID: N/A] Short thread not running.")

                    # **Enhancing Thread Management for Open Positions**
                    # Ensure that we process signals for open positions separately
                    open_position_futures.append(signal_executor.submit(
                        process_signal_for_open_position, 
                        symbol, args, market_maker, manager, symbols_allowed_long, symbols_allowed_short, open_position_data, long_mode, short_mode, graceful_stop_long, graceful_stop_short
                    ))

                # Process new symbols after open positions
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Process new symbols after open positions.")
                if len(active_long_symbols) < symbols_allowed_long or len(active_short_symbols) < symbols_allowed_short:
                    symbols_to_process = whitelist if target_coins_mode else latest_rotator_symbols
                    logging.info(f"Processing symbols from {'whitelist' if target_coins_mode else 'latest rotator symbols'}")
                    logging.info(f"Symbols to process: {symbols_to_process}")

                    for symbol in symbols_to_process:
                        if symbol not in processed_symbols and symbol not in unique_active_symbols:
                            # **Ensure Symbol Limits are Considered Before Processing**
                            with active_symbols_lock:
                                if len(unique_active_symbols) >= manager.symbols_allowed:
                                    logging.info(f"[[{symbol}]](func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Total active symbols ({len(unique_active_symbols)}) have reached the limit ({manager.symbols_allowed}). Skipping new symbol {symbol}.")
                                    break

                                can_open_long = len(active_long_symbols) < symbols_allowed_long and not graceful_stop_long
                                can_open_short = len(active_short_symbols) < symbols_allowed_short and not graceful_stop_short

                            if (can_open_long and long_mode) or (can_open_short and short_mode):
                                signal_futures.append(signal_executor.submit(
                                    process_signal, 
                                    symbol, args, market_maker, manager, symbols_allowed_long, symbols_allowed_short, 
                                    False, can_open_long, can_open_short, graceful_stop_long, graceful_stop_short, 
                                    long_mode, short_mode
                                ))
                                logging.info(f"[[{symbol}]](func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Submitted signal processing for new symbol {symbol}.")
                                processed_symbols.add(symbol)
                                # Not adding to unique_active_symbols here since not yet active
                                time.sleep(2)

                logging.info(f"Submitted signal processing for open position symbols: {open_position_symbols}.")
                process_futures(open_position_futures + signal_futures)

                completed_symbols = []
                # Here we remove completed threads
                # Make sure to use tuple access not dict
                for symbol, (thread, thread_completed) in {**long_threads, **short_threads}.items():
                    if thread_completed.is_set():
                        thread.join()
                        completed_symbols.append(symbol)

                for symbol in completed_symbols:
                    with active_symbols_lock:
                        active_symbols.discard(symbol)
                        if symbol in long_threads:
                            del long_threads[symbol]
                        if symbol in short_threads:
                            del short_threads[symbol]
                        active_long_symbols.discard(symbol)
                        active_short_symbols.discard(symbol)
                        unique_active_symbols.discard(symbol)
                    logging.info(f"Thread and symbol management completed for: {symbol}")

            # Log all threads status periodically
            log_all_threads_status()

            # Also enumerate all threads globally for sanity check
            logging.info("=== Global Thread Enumeration ===")
            for t in threading.enumerate():
                logging.info(f"Thread Name: {t.name}, ID: {t.ident}, Alive: {t.is_alive()}")
            logging.info("================================")

            time.sleep(1)
        except Exception as e:
            logging.info(f"Exception caught in bybit_auto_rotation: {e}")
            logging.info(traceback.format_exc())

        time.sleep(1)

def process_signal_for_open_position(symbol, args, market_maker, manager, symbols_allowed_long, symbols_allowed_short, open_position_data, long_mode, short_mode, graceful_stop_long, graceful_stop_short):
    market_maker.manager = manager

    with general_rate_limiter:
        signal = market_maker.get_signal(symbol)  # Use the appropriate signal based on the entry_signal_type
    logging.info(f"Processing signal for open position symbol {symbol}. Signal: {signal}")

    action_taken = handle_signal_targetcoin(
        symbol, args, manager, signal, open_position_data, 
        symbols_allowed_long, True, long_mode, short_mode, 
        graceful_stop_long, graceful_stop_short, market_maker
    )

    if action_taken:
        logging.info(f"Action taken for open position symbol {symbol}.")
    else:
        logging.info(f"No action taken for open position symbol {symbol}.")

# Neutral signal optimization
def process_signal(symbol, args, market_maker, manager, symbols_allowed_long, symbols_allowed_short,
                   is_open_position, can_open_long, can_open_short, graceful_stop_long,
                   graceful_stop_short, long_mode, short_mode):
    """
    Processes a signal and handles neutral signals efficiently.
    """
    signal = market_maker.get_signal(symbol)

    if signal.lower() == "neutral":
        logging.info(f"Neutral signal for {symbol}. Skipping processing unless re-evaluation is required.")
        return False

    logging.info(f"Processing signal for {symbol}. Signal: {signal}")

    # Existing logic for handling signals (long/short) remains here
    action_taken = handle_signal(
        symbol, args, manager, signal, None, symbols_allowed_long, symbols_allowed_short,
        is_open_position, graceful_stop_long, graceful_stop_short, long_mode, short_mode
    )

    return action_taken

def handle_signal_targetcoin(symbol, args, manager, signal, open_position_data, symbols_allowed_long, is_open_position, long_mode, short_mode, graceful_stop_long, graceful_stop_short, market_maker):
    global unique_active_symbols, active_long_symbols, active_short_symbols

    # Handle None for open_position_data
    if open_position_data is None:
        logging.debug(f"open_position_data is None for symbol {symbol}. Defaulting to empty list.")
        open_position_data = []

    # Log receipt of the signal and handle neutral signals early
    if signal.lower() == "neutral":
        logging.info(f"Received neutral signal for symbol {symbol}. Managing open positions.")
        action_taken = start_thread_for_open_symbol(
            symbol, args, manager, market_maker, signal,
            has_open_long=symbol in active_long_symbols,
            has_open_short=symbol in active_short_symbols,
            long_mode=long_mode, short_mode=short_mode, 
            graceful_stop_long=graceful_stop_long,
            graceful_stop_short=graceful_stop_short
        )
        return action_taken

    # Gather open position symbols and log the current state
    try:
        open_position_symbols = {standardize_symbol(pos['symbol']) for pos in open_position_data}
        logging.info(f"Open position symbols: {open_position_symbols}")
    except Exception as e:
        logging.error(f"Failed to process open_position_data for symbol {symbol}: {e}")
        open_position_symbols = set()

    # Determine the type of signal (long/short)
    signal_long = signal.lower() == "long"
    signal_short = signal.lower() == "short"

    # Log the status of the bot's current positions
    current_long_positions = len(active_long_symbols)
    current_short_positions = len(active_short_symbols)
    logging.info(f"Handling signal for {'open position' if is_open_position else 'new rotator'} symbol {symbol}. "
                 f"Current long positions: {current_long_positions}. "
                 f"Current short positions: {current_short_positions}. "
                 f"Unique active symbols: {len(unique_active_symbols)}")

    logging.info(f"Active long symbols: {active_long_symbols}")
    logging.info(f"Active short symbols: {active_short_symbols}")

    # Check if there are open long/short positions for the symbol
    has_open_long = symbol in active_long_symbols
    has_open_short = symbol in active_short_symbols

    # Log details about the current state and modes
    logging.info(f"{'Open position' if is_open_position else 'New rotator'} symbol {symbol} - "
                 f"Has open long: {has_open_long}, Has open short: {has_open_short}")
    logging.info(f"Signal: {signal}, Long Mode: {long_mode}, Short Mode: {short_mode}")

    # Flags to track if actions are taken
    action_taken_manage_long = False
    action_taken_manage_short = False

    # Determine if the bot can manage a new long/short symbol
    can_manage_new_long_symbol = current_long_positions < symbols_allowed_long
    can_manage_new_short_symbol = current_short_positions < symbols_allowed_short

    # Handle long signals
    if signal_long and long_mode:
        if (can_manage_new_long_symbol or symbol in unique_active_symbols) and not has_open_long:
            if graceful_stop_long and not is_open_position:
                logging.info(f"Skipping long signal for {symbol} due to graceful stop long enabled and no open long position.")
            elif not (symbol in long_threads and long_threads[symbol][0].is_alive()):
                logging.info(f"Starting manage_long thread for symbol {symbol}.")
                action_taken_manage_long = start_thread_for_symbol(
                    symbol=symbol,
                    args=args,
                    manager=manager,
                    market_maker=market_maker,
                    mfirsi_signal=signal,
                    action="manage_long",
                    has_open_long=has_open_long,
                    has_open_short=has_open_short,
                    long_mode=long_mode,
                    short_mode=short_mode,
                    graceful_stop_long=graceful_stop_long,
                    graceful_stop_short=graceful_stop_short
                )
            else:
                logging.info(f"Long thread already running for symbol {symbol}. Skipping.")
        else:
            logging.info(f"Cannot manage long position for {symbol}. Long positions limit reached or position already exists.")

    # Handle short signals
    if signal_short and short_mode:
        if (can_manage_new_short_symbol or symbol in unique_active_symbols) and not has_open_short:
            if graceful_stop_short and not is_open_position:
                logging.info(f"Skipping short signal for {symbol} due to graceful stop short enabled and no open short position.")
            elif not (symbol in short_threads and short_threads[symbol][0].is_alive()):
                logging.info(f"Starting manage_short thread for symbol {symbol}.")
                action_taken_manage_short = start_thread_for_symbol(
                    symbol=symbol,
                    args=args,
                    manager=manager,
                    market_maker=market_maker,
                    mfirsi_signal=signal,
                    action="manage_short",
                    has_open_long=has_open_long,
                    has_open_short=has_open_short,
                    long_mode=long_mode,
                    short_mode=short_mode,
                    graceful_stop_long=graceful_stop_long,
                    graceful_stop_short=graceful_stop_short
                )
            else:
                logging.info(f"Short thread already running for symbol {symbol}. Skipping.")
        else:
            logging.info(f"Cannot manage short position for {symbol}. Short positions limit reached or position already exists.")

    # Update active symbols based on actions taken
    if action_taken_manage_long or action_taken_manage_short:
        with active_symbols_lock:
            unique_active_symbols.add(symbol)
            if action_taken_manage_long:
                active_long_symbols.add(symbol)
            if action_taken_manage_short:
                active_short_symbols.add(symbol)
        logging.info(f"Action taken for {'open position' if is_open_position else 'new rotator'} symbol {symbol}.")
    else:
        logging.info(f"No action taken for {'open position' if is_open_position else 'new rotator'} symbol {symbol}.")

    # Return the result indicating whether any action was taken
    return action_taken_manage_long or action_taken_manage_short

def handle_signal(symbol, args, manager, signal, open_position_data, symbols_allowed_long, symbols_allowed_short, is_open_position, graceful_stop_long, graceful_stop_short, long_mode, short_mode):
    return handle_signal_targetcoin(
        symbol, args, manager, signal, open_position_data, 
        symbols_allowed_long, is_open_position, long_mode, short_mode, 
        graceful_stop_long, graceful_stop_short, manager.market_maker
    )

def manage_rotator_symbols(rotator_symbols, args, manager, symbols_allowed_long, symbols_allowed_short):
    global active_symbols, latest_rotator_symbols

    logging.info(f"Starting symbol management. Total symbols allowed: {symbols_allowed_long + symbols_allowed_short}. Current active symbols: {len(active_symbols)}")

    open_position_data = getattr(manager.exchange, f"get_all_open_positions_{args.exchange.lower()}")()
    open_position_symbols = {standardize_symbol(pos['symbol']) for pos in open_position_data}
    logging.info(f"Currently open positions: {open_position_symbols}")

    current_long_positions = sum(1 for pos in open_position_data if pos['side'].lower() == 'long')
    current_short_positions = sum(1 for pos in open_position_data if pos['side'].lower() == 'short')
    logging.info(f"Current long positions: {current_long_positions}, Current short positions: {current_short_positions}")

    random_rotator_symbols = list(rotator_symbols)
    random.shuffle(random_rotator_symbols)
    logging.info(f"Shuffled rotator symbols for processing: {random_rotator_symbols}")

    for symbol in open_position_symbols:
        process_signal(symbol, args, manager, symbols_allowed_long, symbols_allowed_short, True, False, False, False, False, False, long_mode, short_mode)

    for symbol in random_rotator_symbols:
        if len(open_position_symbols) >= symbols_allowed_long + symbols_allowed_short:
            logging.info("Maximum number of open positions reached.")
            break
        process_signal(symbol, args, manager, symbols_allowed_long, symbols_allowed_short, False, False, False, False, False, False, long_mode, short_mode)

    manage_excess_threads(symbols_allowed_long, symbols_allowed_short, symbols_allowed)
    time.sleep(5)

def manage_excess_threads(symbols_allowed_long, symbols_allowed_short, symbols_allowed):
    global active_symbols, active_long_symbols, active_short_symbols, unique_active_symbols

    with active_symbols_lock:
        # **Prioritize Retaining Threads Managing Open Positions**
        # Attempt to remove threads that are not managing open positions first
        while len(unique_active_symbols) > symbols_allowed:
            # Identify symbols without open positions
            symbols_without_open_positions = unique_active_symbols - active_symbols
            if not symbols_without_open_positions:
                logging.warning("No symbols available to remove without affecting open positions.")
                break  # Exit to avoid removing symbols with open positions

            # Prefer removing short threads first
            symbol_to_remove = next(iter(symbols_without_open_positions))
            if symbol_to_remove in active_short_symbols:
                active_short_symbols.remove(symbol_to_remove)
                remove_thread_for_symbol(symbol_to_remove)
                logging.info(f"Removed short thread to enforce unique symbols limit for symbol: {symbol_to_remove}")
            elif symbol_to_remove in active_long_symbols:
                active_long_symbols.remove(symbol_to_remove)
                remove_thread_for_symbol(symbol_to_remove)
                logging.info(f"Removed long thread to enforce unique symbols limit for symbol: {symbol_to_remove}")
            else:
                logging.warning(f"Symbol {symbol_to_remove} not found in active_long_symbols or active_short_symbols.")
                unique_active_symbols.remove(symbol_to_remove)

        # Enforce per-type limits without affecting symbols with open positions
        excess_long_count = len(active_long_symbols) - symbols_allowed_long
        excess_short_count = len(active_short_symbols) - symbols_allowed_short

        while excess_long_count > 0:
            # Identify long symbols that are not managing open positions
            symbols_can_remove = active_long_symbols - active_symbols
            if not symbols_can_remove:
                logging.warning("No long symbols available to remove without affecting open positions.")
                break

            symbol_to_remove = symbols_can_remove.pop()
            active_long_symbols.remove(symbol_to_remove)
            remove_thread_for_symbol(symbol_to_remove)
            logging.info(f"Removed excess long thread for symbol: {symbol_to_remove}")
            excess_long_count -= 1

        while excess_short_count > 0:
            # Identify short symbols that are not managing open positions
            symbols_can_remove = active_short_symbols - active_symbols
            if not symbols_can_remove:
                logging.warning("No short symbols available to remove without affecting open positions.")
                break

            symbol_to_remove = symbols_can_remove.pop()
            active_short_symbols.remove(symbol_to_remove)
            remove_thread_for_symbol(symbol_to_remove)
            logging.info(f"Removed excess short thread for symbol: {symbol_to_remove}")
            excess_short_count -= 1

def remove_thread_for_symbol(symbol):
    global unique_active_symbols
    if symbol in long_threads:
        thread, thread_completed = long_threads[symbol]
        action = "long"
    elif symbol in short_threads:
        thread, thread_completed = short_threads[symbol]
        action = "short"
    else:
        return

    if thread:
        thread_completed.set()
        thread.join()
        logging.info(f"Removed {action} thread for symbol {symbol}.")

    if symbol in long_threads:
        del long_threads[symbol]
    if symbol in short_threads:
        del short_threads[symbol]
    
    active_long_symbols.discard(symbol)
    active_short_symbols.discard(symbol)
    active_symbols.discard(symbol)
    unique_active_symbols.discard(symbol)

    logging.info(f"Cleaned up symbol {symbol} from active sets.")

def start_thread_for_open_symbol(symbol, args, manager, market_maker, mfirsi_signal, has_open_long, has_open_short, long_mode, short_mode, graceful_stop_long, graceful_stop_short):
    """
    Starts a thread to manage an open position (long or short) for a given symbol.
    """
    global unique_active_symbols, long_threads, short_threads, active_long_symbols, active_short_symbols, active_symbols
    action_taken = False

    # Log the current state of threads for the symbol
    if symbol in long_threads and long_threads[symbol][0].is_alive():
        logging.info(f"A long thread is currently alive for symbol {symbol}.")
    else:
        logging.info(f"No active long thread alive for symbol {symbol}.")

    if symbol in short_threads and short_threads[symbol][0].is_alive():
        logging.info(f"A short thread is currently alive for symbol {symbol}.")
    else:
        logging.info(f"No active short thread alive for symbol {symbol}.")

    # Handle neutral signals by managing open positions
    if mfirsi_signal.lower() == "neutral":
        logging.info(f"Neutral signal received for symbol {symbol}. Managing open positions.")

        if has_open_long and not (symbol in long_threads and long_threads[symbol][0].is_alive()):
            logging.info(f"Attempting to start manage_long thread for symbol {symbol} based on neutral signal.")
            thread_started = start_thread_for_symbol(
                symbol=symbol,
                args=args,
                manager=manager,
                market_maker=market_maker,
                mfirsi_signal=mfirsi_signal,  # Pass the actual signal
                action="manage_long",
                has_open_long=has_open_long,
                has_open_short=has_open_short,
                long_mode=long_mode,
                short_mode=short_mode,
                graceful_stop_long=graceful_stop_long,
                graceful_stop_short=graceful_stop_short
            )
            action_taken = action_taken or thread_started
            logging.info(f"[DEBUG] {'Started' if thread_started else 'Failed to start'} manage_long thread for symbol {symbol} based on neutral signal.")

        if has_open_short and not (symbol in short_threads and short_threads[symbol][0].is_alive()):
            logging.info(f"Attempting to start manage_short thread for symbol {symbol} based on neutral signal.")
            thread_started = start_thread_for_symbol(
                symbol=symbol,
                args=args,
                manager=manager,
                market_maker=market_maker,
                mfirsi_signal=mfirsi_signal,  # Pass the actual signal
                action="manage_short",
                has_open_long=has_open_long,
                has_open_short=has_open_short,
                long_mode=long_mode,
                short_mode=short_mode,
                graceful_stop_long=graceful_stop_long,
                graceful_stop_short=graceful_stop_short
            )
            action_taken = action_taken or thread_started
            logging.info(f"[DEBUG] {'Started' if thread_started else 'Failed to start'} manage_short thread for symbol {symbol} based on neutral signal.")

    else:
        # Handle non-neutral signals
        if long_mode and has_open_long and not graceful_stop_long and not (symbol in long_threads and long_threads[symbol][0].is_alive()):
            logging.info(f"Attempting to start manage_long thread for open symbol {symbol}.")
            thread_started = start_thread_for_symbol(
                symbol=symbol,
                args=args,
                manager=manager,
                market_maker=market_maker,
                mfirsi_signal=mfirsi_signal,  # Pass the actual signal
                action="manage_long",
                has_open_long=has_open_long,
                has_open_short=has_open_short,
                long_mode=long_mode,
                short_mode=short_mode,
                graceful_stop_long=graceful_stop_long,
                graceful_stop_short=graceful_stop_short
            )
            action_taken = action_taken or thread_started
            logging.info(f"[DEBUG] {'Started' if thread_started else 'Failed to start'} manage_long thread for open symbol {symbol}.")

        if short_mode and has_open_short and not graceful_stop_short and not (symbol in short_threads and short_threads[symbol][0].is_alive()):
            logging.info(f"Attempting to start manage_short thread for open symbol {symbol}.")
            thread_started = start_thread_for_symbol(
                symbol=symbol,
                args=args,
                manager=manager,
                market_maker=market_maker,
                mfirsi_signal=mfirsi_signal,  # Pass the actual signal
                action="manage_short",
                has_open_long=has_open_long,
                has_open_short=has_open_short,
                long_mode=long_mode,
                short_mode=short_mode,
                graceful_stop_long=graceful_stop_long,
                graceful_stop_short=graceful_stop_short
            )
            action_taken = action_taken or thread_started
            logging.info(f"[DEBUG] {'Started' if thread_started else 'Failed to start'} manage_short thread for open symbol {symbol}.")

    # Log if no action was taken
    if not action_taken:
        logging.info(f"No thread started for open symbol {symbol}.")

    return action_taken

def start_thread_for_symbol(symbol, args, manager, market_maker, mfirsi_signal, action,
                            has_open_long, has_open_short, long_mode, short_mode,
                            graceful_stop_long, graceful_stop_short):
    logging.debug(f"Starting thread for symbol: {symbol}, action: {action}, signal: {mfirsi_signal}")
    """
    Starts a thread to manage an open position for a given symbol.

    :param symbol: Trading pair (e.g., 'MEUSDT')
    :param args: Command-line arguments or configurations
    :param manager: Manager instance handling exchange interactions
    :param market_maker: MarketMaker instance handling strategies
    :param mfirsi_signal: Current signal ('neutral', 'long', 'short')
    :param action: Action to perform ('manage_long', 'manage_short')
    :param has_open_long: Boolean indicating existing long position
    :param has_open_short: Boolean indicating existing short position
    :param long_mode: Flag indicating if long strategies are active
    :param short_mode: Flag indicating if short strategies are active
    :param graceful_stop_long: Flag for graceful stopping of long positions
    :param graceful_stop_short: Flag for graceful stopping of short positions
    :return: Boolean indicating if the thread was successfully started
    """
    global unique_active_symbols, long_threads, short_threads, active_long_symbols, active_short_symbols, active_symbols

    # action_taken = False

    if not can_spawn_thread(symbol):  # Check cooldown
        return False  # Skip spawning if cooldown is active

    # Check if there's already a running thread for this symbol/action
    if action == "manage_long" and symbol in long_threads and long_threads[symbol][0].is_alive():
        logging.info(f"Long thread already running for symbol {symbol}. Skipping.")
        return False
    elif action == "manage_short" and symbol in short_threads and short_threads[symbol][0].is_alive():
        logging.info(f"Short thread already running for symbol {symbol}. Skipping.")
        return False

    # Prepare the thread
    thread_completed = threading.Event()
    thread = threading.Thread(
        target=run_bot,
        args=(
            symbol, args, market_maker, manager, args.account_name,
            manager.symbols_allowed_long, manager.symbols_allowed_short,
            latest_rotator_symbols, thread_completed, mfirsi_signal, action
        )
    )
    # Name the thread to include symbol and action
    thread.name = f"run_bot({symbol}, {action})"

    # Acquire the lock to ensure that no other threads can modify counts while we check conditions
    with active_symbols_lock:
        # Determine if this symbol is already actively managed in the corresponding set
        # If it is, we allow managing the position even if limits are reached
        already_long = symbol in active_long_symbols
        already_short = symbol in active_short_symbols

        current_long_positions = len(active_long_symbols)
        current_short_positions = len(active_short_symbols)
        current_unique_symbols = len(unique_active_symbols)

        # Re-check conditions within the lock
        if action == "manage_long":
            # If not already open as a long position, check limits
            if not already_long:
                if current_long_positions >= manager.symbols_allowed_long:
                    logging.info(f"Cannot open a new long position for symbol {symbol} because the long limit ({manager.symbols_allowed_long}) has been reached.")
                    return False
                if current_unique_symbols >= manager.symbols_allowed:
                    logging.info(f"Cannot open a new position for symbol {symbol} because the total symbol limit ({manager.symbols_allowed}) has been reached.")
                    return False

            # Conditions are met or symbol is already managed long; proceed
            long_threads[symbol] = (thread, thread_completed)
            active_long_symbols.add(symbol)
            active_symbols.add(symbol)
            unique_active_symbols.add(symbol)

        elif action == "manage_short":
            # If not already open as a short position, check limits
            if not already_short:
                if current_short_positions >= manager.symbols_allowed_short:
                    logging.info(f"Cannot open a new short position for symbol {symbol} because the short limit ({manager.symbols_allowed_short}) has been reached.")
                    return False
                if current_unique_symbols >= manager.symbols_allowed:
                    logging.info(f"Cannot open a new position for symbol {symbol} because the total symbol limit ({manager.symbols_allowed}) has been reached.")
                    return False

            # Conditions are met or symbol is already managed short; proceed
            short_threads[symbol] = (thread, thread_completed)
            active_short_symbols.add(symbol)
            active_symbols.add(symbol)
            unique_active_symbols.add(symbol)

        # Try starting the thread
        try:
            thread.start()
            logging.info(f"Started thread for symbol {symbol} with action {action}.")
            return True
        except Exception as e:
            logging.error(f"Failed to start thread for symbol {symbol} with action {action}: {e}")
            # Roll back changes if thread fails to start
            if action == "manage_long":
                long_threads.pop(symbol, None)
                active_long_symbols.discard(symbol)
                active_symbols.discard(symbol)
                unique_active_symbols.discard(symbol)
            elif action == "manage_short":
                short_threads.pop(symbol, None)
                active_short_symbols.discard(symbol)
                active_symbols.discard(symbol)
                unique_active_symbols.discard(symbol)
            return False

    # return action_taken

def fetch_updated_symbols(args, manager, config, whitelist=None):  # CHANGED: Added 'config' parameter
    current_time = time.time()
    
    # Check if the cached data is still valid
    if current_time - rotator_symbols_cache['timestamp'] < CACHE_DURATION:
        logging.info(f"Using cached rotator symbols")
        return rotator_symbols_cache['symbols']
    
    # Fetch new data if cache is expired
    strategy = args.strategy.lower()
    potential_symbols = []

    # Access blacklist and max_usd_value from config
    blacklist = config.bot.blacklist
    max_usd_value = config.bot.max_usd_value

    if whitelist:
        potential_symbols = [symbol for symbol in whitelist]
    else:
        if strategy == 'basicgrid':
            potential_bullish_symbols = manager.get_bullish_rotator_symbols(min_qty_threshold=None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
            potential_bearish_symbols = manager.get_bearish_rotator_symbols(min_qty_threshold=None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
            potential_symbols = potential_bullish_symbols + potential_bearish_symbols
        elif strategy == 'basicgridmfirsi':
            potential_bullish_symbols = manager.get_bullish_rotator_symbols(min_qty_threshold=None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
            potential_bearish_symbols = manager.get_bearish_rotator_symbols(min_qty_threshold=None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
            potential_symbols = potential_bullish_symbols + potential_bearish_symbols
        elif strategy == 'qstrendlongonly':
            potential_symbols = manager.get_bullish_rotator_symbols(min_qty_threshold=None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
        elif strategy == 'qstrendshortonly':
            potential_symbols = manager.get_bearish_rotator_symbols(min_qty_threshold=None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
        else:
            potential_symbols = manager.get_auto_rotate_symbols(min_qty_threshold=None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)

    # Update the cache with new data and timestamp
    rotator_symbols_cache['symbols'] = set(standardize_symbol(sym) for sym in potential_symbols)
    rotator_symbols_cache['timestamp'] = current_time
    
    logging.info(f"Fetched new rotator symbols: {rotator_symbols_cache['symbols']}")
    return rotator_symbols_cache['symbols']

def log_symbol_details(strategy, symbols):
    logging.info(f"Potential symbols for {strategy}: {symbols}")


# Enhanced position limit logging
def enforce_position_limits():
    """
    Logs detailed information about position limits and enforces them dynamically.
    """
    global active_long_symbols, active_short_symbols

    current_long_positions = len(active_long_symbols)
    current_short_positions = len(active_short_symbols)

    logging.info(f"Enforcing position limits: Long - {current_long_positions}/{manager.symbols_allowed_long}, "
                 f"Short - {current_short_positions}/{manager.symbols_allowed_short}")

    if current_long_positions > manager.symbols_allowed_long:
        logging.warning(f"Long position limit exceeded. Current: {current_long_positions}, Allowed: {manager.symbols_allowed_long}.")

    if current_short_positions > manager.symbols_allowed_short:
        logging.warning(f"Short position limit exceeded. Current: {current_short_positions}, Allowed: {manager.symbols_allowed_short}.")

# Initialize colorama with autoreset
init(autoreset=True)

if __name__ == '__main__':
    sword = f"{Fore.CYAN}====={Fore.WHITE}||{Fore.RED}====>"

    # Display introductory messages and ASCII art
    print("\n" + Fore.YELLOW + "=" * 60)
    print(Fore.CYAN + Style.BRIGHT + f"DirectionalScalper {VERSION}".center(60))
    print(Fore.GREEN + f"Developed by Tyler Simpson and contributors at".center(60))
    print(Fore.GREEN + f"Quantum Void Labs".center(60))
    print(Fore.YELLOW + "=" * 60 + "\n")

    print(Fore.WHITE + "Initializing", end="")
    for i in range(3):
        time.sleep(0.5)
        print(Fore.YELLOW + ".", end="", flush=True)
    print("\n")

    print(Fore.MAGENTA + Style.BRIGHT + "Battle-Ready Algorithm".center(60))
    print(sword.center(73) + "\n")  # Adjusted for color codes

    # ASCII Art
    ascii_art = r"""
    ⚔️  Prepare for Algorithmic Conquest  ⚔️
      _____   _____   _____   _____   _____
     /     \ /     \ /     \ /     \ /     \
    /       V       V       V       V       \
   |     DirectionalScalper Activated     |
    \       ^       ^       ^       ^       /
     \_____/ \_____/ \_____/ \_____/ \_____/
    """
    
    print(Fore.CYAN + ascii_art)

    # Simulated loading bar
    print(Fore.YELLOW + "Loading trading modules:")
    for i in range(101):
        time.sleep(0.03)  # Adjust speed as needed
        print(f"\r[{'=' * (i // 2)}{' ' * (50 - i // 2)}] {i}%", end="", flush=True)
    print("\n")

    print(Fore.GREEN + Style.BRIGHT + "DirectionalScalper is ready for battle!")
    print(Fore.RED + "May the odds be ever in your favor.\n")

    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='DirectionalScalper')
    parser.add_argument('--config', type=str, default='configs/config.json', help='Path to the configuration file')
    parser.add_argument('--account_name', type=str, help='The name of the account to use')
    parser.add_argument('--exchange', type=str, help='The name of the exchange to use')
    parser.add_argument('--strategy', type=str, help='The name of the strategy to use')
    parser.add_argument('--symbol', type=str, help='The trading symbol to use')
    parser.add_argument('--amount', type=str, help='The size to use')

    args = parser.parse_args()
    args = ask_for_missing_arguments(args)

    print(f"DirectionalScalper {VERSION} Initialized Successfully!".center(50))
    print("=" * 50 + "\n")

    # Load configuration files
    config_file_path = Path(args.config)
    account_path = Path('configs/account.json')

    try:
        config = load_config(config_file_path, account_path)
    except Exception as e:
        logging.error(f"Failed to load configuration: {str(e)}")
        logging.error(f"There is probably an issue with your path try using --config configs/config.json")
        sys.exit(1)

    exchange_name = args.exchange
    try:
        market_maker = DirectionalMarketMaker(config, exchange_name, args.account_name)
    except Exception as e:
        logging.error(f"Failed to initialize market maker: {str(e)}")
        sys.exit(1)


    # Extract symbols_allowed, symbols_allowed_long, symbols_allowed_short from config
    for exch in config.exchanges:
        if exch.name.lower() == exchange_name.lower() and exch.account_name == args.account_name:
            symbols_allowed = exch.symbols_allowed
            symbols_allowed_long = exch.symbols_allowed_long
            symbols_allowed_short = exch.symbols_allowed_short
            logging.info(f"Data read from config- symbols_allowed: {symbols_allowed}, Long: {symbols_allowed_long}, Short: {symbols_allowed_short}")
            
            break
    else:
        symbols_allowed = 2
        symbols_allowed_long = 1
        symbols_allowed_short = 1
        logging.warning(
            f"No matching exchange configuration found for exchange: {exchange_name} and account: {args.account_name}. "
            f"Using default symbols_allowed: {symbols_allowed}, symbols_allowed_long: {symbols_allowed_long}, symbols_allowed_short: {symbols_allowed_short}."
        )
    # Instantiate Manager with symbol limits
    manager = Manager(
        market_maker.exchange,
        exchange_name=args.exchange,
        data_source_exchange=config.api.data_source_exchange,
        api=config.api.mode,
        path=Path("data", config.api.filename),
        url=f"{config.api.url}{config.api.filename}",
        symbols_allowed=symbols_allowed,
        symbols_allowed_long=symbols_allowed_long,
        symbols_allowed_short=symbols_allowed_short
    )

    # Establish the two-way reference
    market_maker.manager = manager
    manager.market_maker = market_maker

    print(f"Using exchange {config.api.data_source_exchange} for API data")

    whitelist = config.bot.whitelist
    blacklist = config.bot.blacklist
    max_usd_value = config.bot.max_usd_value


    # Initialize live table manager and start its display thread
    table_manager = LiveTableManager()  # CHANGED
    display_thread = threading.Thread(target=table_manager.display_table)
    display_thread.daemon = True
    display_thread.start()

    # Main loop to handle auto-rotation based on exchange
    while True:
        try:
            whitelist = config.bot.whitelist
            blacklist = config.bot.blacklist
            max_usd_value = config.bot.max_usd_value

            match exchange_name.lower():
                case 'bybit':
                    bybit_auto_rotation(args, market_maker, manager, symbols_allowed_long, symbols_allowed_short)
                case _:
                    logging.warning(f"Auto-rotation not implemented for exchange: {exchange_name}")

            logging.info(f"Active symbols: {active_symbols}")
            logging.info(f"Total active symbols: {len(active_symbols)}")

            time.sleep(10)
        except Exception as e:
            logging.info(f"Exception caught in main loop: {e}")
            logging.info(traceback.format_exc())
