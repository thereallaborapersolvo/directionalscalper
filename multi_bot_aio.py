# multi_bot_aio.py
import sys
import os
import time
from concurrent.futures import ThreadPoolExecutor, as_completed, Future
import threading
from threading import Thread
import atexit
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

active_symbols_lock = threading.Lock()  # New Lock for Synchronizing Active Symbol Counts
thread_info_lock = threading.Lock()     # New Lock for Thread Info Logging

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
symbol_last_spawn_time = {}
symbol_next_attempt_time = {}  # Tracks earliest time we can attempt spawning a new thread for a symbol


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
        thread_completed=None,
        trading_executor=None  # New parameter
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
        if not strategy_class:
            logging.error(f"Strategy {strategy_name} not found.")
            future_err = Future()
            future_err.set_exception(ValueError(f"Strategy {strategy_name} not found."))
            return future_err

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
                future_long = trading_executor.submit(
                    self.run_with_future,
                    strategy,
                    symbol,
                    rotator_symbols_standardized,
                    mfirsi_signal,
                    "long",
                    thread_completed
                )
                return future_long
            elif action in ["manage_short", "short"]:
                future_short = trading_executor.submit(
                    self.run_with_future,
                    strategy,
                    symbol,
                    rotator_symbols_standardized,
                    mfirsi_signal,
                    "short",
                    thread_completed
                )
                return future_short
            else:
                future_no_op = Future()
                future_no_op.set_result(True)
                return future_no_op
        except Exception as e:
            logging.error(f"Exception in run_strategy for {symbol}: {e}")
            future_exc = Future()
            future_exc.set_exception(e)
            return future_exc

    def run_with_future(self, strategy, symbol, rotator_symbols_standardized, mfirsi_signal, action, thread_completed):
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
        except Exception as e:
            logging.error(f"Exception in run_with_future for {symbol}, action={action}: {e}")
            logging.error(traceback.format_exc())
            raise  # Let the executor handle the exception

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
        logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Generating signal for symbol: {symbol} using entry_signal_type: {self.entry_signal_type}")
        if self.entry_signal_type == 'mfirsi_signal':
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Using mfirsi signals for symbol {symbol}")
            signal = self.get_mfirsi_signal(symbol)
        elif self.entry_signal_type == 'lorentzian':
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Using lorentzian signals for symbol {symbol}")
            signal = self.generate_l_signals(symbol)
        else:
            raise ValueError(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Unknown entry signal type: {self.entry_signal_type}")

        logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Generated signal for {symbol}: {signal}")
        if signal == "neutral":
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Skipping processing for {symbol} due to neutral signal.")
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
    method_name = f"get_all_open_positions_{exchange_name.lower()}"
    
    # Check if the method exists
    if not hasattr(manager.exchange, method_name):
        logging.error(f"({inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) "
                      f"Exchange '{exchange_name}' does not have method '{method_name}'.")
        return False  # Or handle as appropriate
    
    # Retrieve position data
    pos_data = getattr(manager.exchange, method_name)()
    
    # Determine if there's a long position for the symbol
    is_long = any(
        standardize_symbol(pos['symbol']) == symbol and pos['side'].lower() == 'long'
        for pos in pos_data
    )
    
    logging.debug(f"({inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) "
                  f"Checked if '{symbol}' is a long position: {is_long}")
    
    return is_long


def is_short_position(symbol, manager, exchange_name):
    method_name = f"get_all_open_positions_{exchange_name.lower()}"
    
    # Check if the method exists
    if not hasattr(manager.exchange, method_name):
        logging.error(f"({inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) "
                      f"Exchange '{exchange_name}' does not have method '{method_name}'.")
        return False  # Or handle as appropriate
    
    # Retrieve position data
    pos_data = getattr(manager.exchange, method_name)()
    
    # Determine if there's a short position for the symbol
    is_short = any(
        standardize_symbol(pos['symbol']) == symbol and pos['side'].lower() == 'short'
        for pos in pos_data
    )
    
    logging.debug(f"({inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) "
                  f"Checked if '{symbol}' is a short position: {is_short}")
    
    return is_short


def update_active_symbols(open_position_symbols, manager, exchange_name):
    global active_symbols, active_long_symbols, active_short_symbols, unique_active_symbols
    with active_symbols_lock:
        active_symbols = open_position_symbols
        active_long_symbols = {symbol for symbol in open_position_symbols if is_long_position(symbol, manager, exchange_name)}
        active_short_symbols = {symbol for symbol in open_position_symbols if is_short_position(symbol, manager, exchange_name)}
        unique_active_symbols = active_long_symbols.union(active_short_symbols)
        logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated active symbols ({len(active_symbols)}): {active_symbols}")
        logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated active long symbols ({len(active_long_symbols)}): {active_long_symbols}")
        logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated active short symbols ({len(active_short_symbols)}): {active_short_symbols}")
        logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated unique active symbols ({len(unique_active_symbols)}): {unique_active_symbols}")

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

def run_bot(symbol, args, market_maker, manager, account_name, symbols_allowed_long, symbols_allowed_short, rotator_symbols_standardized, thread_completed, mfirsi_signal, action, trading_executor):
    """
    Runs the trading bot logic for a given symbol.
    """
    global orders_canceled, unique_active_symbols, active_long_symbols, active_short_symbols
    logging.info(f"Task started for symbol: {symbol}, action: {action}")
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
                thread_completed=thread_completed,
                trading_executor=trading_executor  # Pass it here
            )

            logging.debug(f"[run_bot] run_strategy returned future={future} for {symbol}")

            # Block until the internal strategy completes
            result = future.result()
            logging.debug(f"[run_bot] Strategy completed for {symbol}, result={result}")

        # Monitor the position in a loop until it's closed
        while True:
            # Continuously monitor the position
            try:
                open_position_data_final = getattr(manager.exchange, f"get_all_open_positions_{exchange_name.lower()}")()
                open_symbol_set_final = {standardize_symbol(pos['symbol']) for pos in open_position_data_final}
                position_still_open = (symbol in open_symbol_set_final)

                if not position_still_open:
                    logging.info(f"Position closed for {symbol}. Cleaning up.")
                    break  # Exit the loop and allow task to terminate

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
                logging.info(f"Task completed for {symbol}, exchange shows position closed. Removing from active sets.")
                active_symbols.discard(symbol)
                if action == "manage_long":
                    active_long_symbols.discard(symbol)
                elif action == "manage_short":
                    active_short_symbols.discard(symbol)
                unique_active_symbols.discard(symbol)
                logging.info(f"Removed {symbol} from active sets.")
            else:
                # Position is still open; the current task continues managing it
                logging.info(f"Task for {symbol} is continuing to manage an open position.")

        logging.info(f"Task completed for symbol: {symbol}, action: {action}")
        # **UPDATED**: Make sure we set the same event that was passed in from start_thread_for_symbol
        thread_completed.set()


# New helper function for regular thread monitoring
def log_all_threads_status():
    logging.info("=== Current Active Futures ===")
    for symbol, (future, completed_event) in long_threads.items():
        status = "Done" if future.done() else "Running"
        cancelled = future.cancelled()
        exception = future.exception() if future.done() else None
        logging.info(f"LONG FUTURE for {symbol}: Status={status}, Cancelled={cancelled}, Exception={exception}")
    for symbol, (future, completed_event) in short_threads.items():
        status = "Done" if future.done() else "Running"
        cancelled = future.cancelled()
        exception = future.exception() if future.done() else None
        logging.info(f"SHORT FUTURE for {symbol}: Status={status}, Cancelled={cancelled}, Exception={exception}")
    logging.info("================================")

def bybit_auto_rotation(args, market_maker, manager, symbols_allowed_long, symbols_allowed_short):
    """
    Perform auto-rotation of symbols for Bybit exchange.
    """
    global latest_rotator_symbols, long_threads, short_threads, active_symbols, active_long_symbols, active_short_symbols, last_rotator_update_time, unique_active_symbols
    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Starting bybit_auto_rotation.")
    
    # Define the number of workers
    max_workers_signals = 1
    max_workers_trading = 5  # Increased from 1 to 5

    # Initialize executors
    signal_executor = ThreadPoolExecutor(max_workers=max_workers_signals)
    trading_executor = ThreadPoolExecutor(max_workers=max_workers_trading)

    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Initialized signal_executor with max workers: {max_workers_signals}")
    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Initialized trading_executor with max workers: {max_workers_trading}")

    # Register shutdown procedures to ensure executors are closed gracefully
    atexit.register(lambda: trading_executor.shutdown(wait=True))
    atexit.register(lambda: signal_executor.shutdown(wait=True))

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

    def process_futures(futures, timeout=30):
        try:
            for fut in as_completed(futures, timeout=timeout):
                try:
                    fut.result()
                    logging.info("Future completed successfully.")
                except Exception as e:
                    logging.error(f"Exception in thread: {e}")
                    logging.debug(traceback.format_exc())
        except TimeoutError:
            logging.error("Timeout occurred while waiting for futures to complete.")

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
                    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) GS Auto Check: Automatically enabled graceful stop for long positions. Current long positions: {current_long_positions}, Active long symbols: {len(active_long_symbols)}")
                elif current_long_positions < symbols_allowed_long and len(active_long_symbols) < symbols_allowed_long and graceful_stop_long:
                    graceful_stop_long = config_graceful_stop_long
                    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) GS Auto Check: Reverting to config value for graceful stop long. Current long positions: {current_long_positions}, Active long symbols: {len(active_long_symbols)}, Config value: {config_graceful_stop_long}")
                else:
                    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) GS Auto Check: Current long positions: {current_long_positions}, Active long symbols: {len(active_long_symbols)}. Graceful stop long: {graceful_stop_long}")

                if (current_short_positions >= symbols_allowed_short or len(active_short_symbols) >= symbols_allowed_short) and not graceful_stop_short:
                    graceful_stop_short = True
                    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) GS Auto Check: Automatically enabled graceful stop for short positions. Current short positions: {current_short_positions}, Active short symbols: {len(active_short_symbols)}")
                elif current_short_positions < symbols_allowed_short and len(active_short_symbols) < symbols_allowed_short and graceful_stop_short:
                    graceful_stop_short = config_graceful_stop_short
                    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) GS Auto Check: Reverting to config value for graceful stop short. Current short positions: {current_short_positions}, Active short symbols: {len(active_short_symbols)}, Config value: {config_graceful_stop_short}")
                else:
                    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) GS Auto Check: Current short positions: {current_short_positions}, Active short symbols: {len(active_short_symbols)}. Graceful stop short: {graceful_stop_short}")

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
                logging.debug(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) No refresh needed yet. Last update was at {last_rotator_update_time}, less than 60 seconds ago.")

            with thread_management_lock:
                open_position_futures = []
                signal_futures = []

                # Process signals for open positions
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno})  Process signals for open positions.")
                for symbol in open_position_symbols.copy():
                    open_position_futures.append(trading_executor.submit(
                        process_signal_for_open_position, 
                        symbol, args, market_maker, manager, symbols_allowed_long, symbols_allowed_short,
                        open_position_data, long_mode, short_mode, graceful_stop_long, graceful_stop_short,
                        trading_executor
                    ))

                # Process new symbols after open positions
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) (func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Process new symbols after open positions.")
                if len(active_long_symbols) < symbols_allowed_long or len(active_short_symbols) < symbols_allowed_short:
                    symbols_to_process = whitelist if target_coins_mode else latest_rotator_symbols
                    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Processing symbols from {'whitelist' if target_coins_mode else 'latest rotator symbols'}")
                    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Symbols to process: {symbols_to_process}")

                    for symbol in symbols_to_process:
                        if symbol not in processed_symbols and symbol not in unique_active_symbols:
                            # **Ensure Symbol Limits are Considered Before Processing**
                            with active_symbols_lock:
                                if len(unique_active_symbols) >= manager.symbols_allowed:
                                    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [{symbol}] Total active symbols ({len(unique_active_symbols)}) have reached the limit ({manager.symbols_allowed}). Skipping new symbol {symbol}.")
                                    break

                                can_open_long = len(active_long_symbols) < symbols_allowed_long and not graceful_stop_long
                                can_open_short = len(active_short_symbols) < symbols_allowed_short and not graceful_stop_short

                            if (can_open_long and long_mode) or (can_open_short and short_mode):
                                signal_futures.append(trading_executor.submit(
                                    process_signal, 
                                    symbol, args, market_maker, manager, symbols_allowed_long, symbols_allowed_short, 
                                    False, can_open_long, can_open_short, graceful_stop_long, graceful_stop_short, 
                                    long_mode, short_mode, trading_executor
                                ))
                                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [{symbol}] Submitted signal processing for new symbol {symbol}.")
                                processed_symbols.add(symbol)
                                # Not adding to unique_active_symbols here since not yet active
                                time.sleep(2)

                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Submitted signal processing for open position symbols: {open_position_symbols}.")
                process_futures(open_position_futures + signal_futures)

                completed_symbols = []
                # **UPDATED**: we check if the future is done or if the event is set
                for symbol, (future, completed_event) in {**long_threads, **short_threads}.items():
                    # If the event is set or the future is done, we consider the thread finished
                    if completed_event.is_set() or future.done():
                        # If you want to retrieve result, do future.result() 
                        _ = future.result()  # or just ignore if not needed
                        completed_symbols.append(symbol)

                for symbol in completed_symbols:
                    with active_symbols_lock:
                        if symbol in long_threads:
                            del long_threads[symbol]
                        if symbol in short_threads:
                            del short_threads[symbol]
                        active_symbols.discard(symbol)
                        active_long_symbols.discard(symbol)
                        active_short_symbols.discard(symbol)
                        unique_active_symbols.discard(symbol)
                    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Thread and symbol management completed for: {symbol}")

            # Log all threads status periodically
            log_all_threads_status()

            # Also enumerate all threads globally for sanity check
            logging.info("=== Global Thread Enumeration ===")
            for t in threading.enumerate():
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Thread Name: {t.name}, ID: {t.ident}, Alive: {t.is_alive()}")
            logging.info("================================")

            time.sleep(1)
        except Exception as e:
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Exception caught in bybit_auto_rotation: {e}")
            logging.info(traceback.format_exc())

        time.sleep(1)

def process_signal_for_open_position(symbol, args, market_maker, manager, symbols_allowed_long, symbols_allowed_short, open_position_data, long_mode, short_mode, graceful_stop_long, graceful_stop_short, trading_executor):
    """
    Processes a signal for open positions and submits tasks via trading_executor.
    """
    market_maker.manager = manager

    logging.info(f"Processing open position for symbol: {symbol}")
    try:
        with general_rate_limiter:
            signal = market_maker.get_signal(symbol)  # Use the appropriate signal based on the entry_signal_type
        logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Processing signal for open position symbol {symbol}. Signal: {signal}")

        # Define is_position_open based on open_position_data
        is_position_open = symbol in {standardize_symbol(pos['symbol']) for pos in open_position_data}

        action_taken = handle_signal_targetcoin(
            symbol, args, manager, signal, open_position_data, 
            symbols_allowed_long, symbols_allowed_short, is_position_open, long_mode, short_mode, 
            graceful_stop_long, graceful_stop_short, market_maker, trading_executor
        )

        if action_taken:
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Action taken for open position symbol {symbol}.")
        else:
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) No action taken for open position symbol {symbol}.")
        
        logging.info(f"Successfully processed open position for symbol: {symbol}")
    except Exception as e:
        logging.error(f"Error processing open position for symbol {symbol}: {e}")
        logging.debug(traceback.format_exc())

# Neutral signal optimization
def process_signal(symbol, args, market_maker, manager, symbols_allowed_long, symbols_allowed_short,
                   is_open_position, can_open_long, can_open_short, graceful_stop_long,
                   graceful_stop_short, long_mode, short_mode, trading_executor):
    """
    Processes a signal and handles neutral signals efficiently.
    """
    logging.info(f"Processing new signal for symbol: {symbol}")
    try:
        signal = market_maker.get_signal(symbol)

        if signal.lower() == "neutral":
            logging.info(f"Neutral signal for {symbol}. Skipping processing unless re-evaluation is required.")
            return False

        logging.info(f"Processing signal for {symbol}. Signal: {signal}")

        # Existing logic for handling signals (long/short) remains here
        action_taken = handle_signal(
            symbol, args, manager, signal, None, symbols_allowed_long, symbols_allowed_short,
            is_open_position, graceful_stop_long, graceful_stop_short, long_mode, short_mode, trading_executor
        )

        logging.info(f"Successfully processed signal for symbol: {symbol}")
    except Exception as e:
        logging.error(f"Error processing signal for symbol {symbol}: {e}")
        logging.debug(traceback.format_exc())
    return action_taken


def handle_signal_targetcoin(symbol, args, manager, signal, open_position_data, 
                             symbols_allowed_long, symbols_allowed_short, is_open_position,
                             long_mode, short_mode, graceful_stop_long, graceful_stop_short,
                             market_maker, trading_executor):
    global unique_active_symbols, active_long_symbols, active_short_symbols

    signal_lower = signal.lower()
    signal_long = (signal_lower == "long")
    signal_short = (signal_lower == "short")
    signal_neutral = (signal_lower == "neutral")

    current_long_positions = len(active_long_symbols)
    current_short_positions = len(active_short_symbols)

    has_open_long = symbol in active_long_symbols
    has_open_short = symbol in active_short_symbols

    logging.info(
        f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Handling signal for {'open' if is_open_position else 'new'} symbol {symbol}. "
        f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Active longs: {current_long_positions}, Active shorts: {current_short_positions}, "
        f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) signal={signal}, has_open_long={has_open_long}, has_open_short={has_open_short}"
    )

    action_taken_manage_long = False
    action_taken_manage_short = False

    # Handle neutral signals early
    if signal_neutral:
        logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Received neutral signal for symbol {symbol}. Managing open positions.")

        if has_open_long:
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Attempting to manage existing long position for symbol {symbol} based on neutral signal.")
            action_taken_manage_long = start_thread_for_symbol(
                symbol, args, manager, market_maker,
                signal, "manage_long",
                has_open_long, has_open_short,
                long_mode, short_mode,
                graceful_stop_long, graceful_stop_short, trading_executor
            )

        if has_open_short:
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Attempting to manage existing short position for symbol {symbol} based on neutral signal.")
            action_taken_manage_short = start_thread_for_symbol(
                symbol, args, manager, market_maker,
                signal, "manage_short",
                has_open_long, has_open_short,
                long_mode, short_mode,
                graceful_stop_long, graceful_stop_short, trading_executor
            )

        return action_taken_manage_long or action_taken_manage_short

    # Handle long signals
    if signal_long and long_mode:
        if has_open_long:
            # Already have a long position: just manage it if no task is running.
            if symbol in long_threads and not long_threads[symbol][0].done():
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Long task already running for symbol {symbol}. Skipping.")
            else:
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Attempting to manage existing long position for symbol {symbol}.")
                action_taken_manage_long = start_thread_for_symbol(
                    symbol, args, manager, market_maker,
                    signal, "manage_long",
                    has_open_long, has_open_short,
                    long_mode, short_mode,
                    graceful_stop_long, graceful_stop_short, trading_executor
                )
        else:
            # No open long position: treat as new symbol
            # Rely on start_thread_for_symbol for final limit checks
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Attempting to open/manage long for new symbol {symbol}.")
            if symbol in long_threads and not long_threads[symbol][0].done():
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Long task already running for symbol {symbol}. Skipping.")
            else:
                    action_taken_manage_long = start_thread_for_symbol(
                    symbol, args, manager, market_maker,
                    signal, "manage_long",
                    has_open_long, has_open_short,
                    long_mode, short_mode,
                    graceful_stop_long, graceful_stop_short, trading_executor
                    )

    # If symbol already has a short position, re-manage it without limit checks
    if signal_short and short_mode:
        if has_open_short:
            # Already have a short position
            if symbol in short_threads and not short_threads[symbol][0].done():
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Short task already running for symbol {symbol}. Skipping.")
            else:
                logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Attempting to manage existing short position for symbol {symbol}.")
                action_taken_manage_short = start_thread_for_symbol(
                    symbol, args, manager, market_maker,
                    signal, "manage_short",
                    has_open_long, has_open_short,
                    long_mode, short_mode,
                    graceful_stop_long, graceful_stop_short, trading_executor
                )
        else:
            # No open short position: treat as new symbol
            logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Attempting to open/manage short for new symbol {symbol}.")
            if symbol in short_threads and not short_threads[symbol][0].done():
                logging.info(f"Short task already running for symbol {symbol}. Skipping.")
            else:
                    action_taken_manage_short = start_thread_for_symbol(
                    symbol, args, manager, market_maker,
                    signal, "manage_short",
                    has_open_long, has_open_short,
                    long_mode, short_mode,
                    graceful_stop_long, graceful_stop_short, trading_executor
                    )

    return action_taken_manage_long or action_taken_manage_short

def handle_signal(symbol, args, manager, signal, open_position_data, 
                  symbols_allowed_long, symbols_allowed_short, is_open_position,
                  graceful_stop_long, graceful_stop_short, long_mode, short_mode,
                  trading_executor):
    return handle_signal_targetcoin(
        symbol, args, manager, signal, open_position_data, 
        symbols_allowed_long, symbols_allowed_short, is_open_position,
        long_mode, short_mode, graceful_stop_long, graceful_stop_short,
        manager.market_maker, trading_executor
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
        process_signal(symbol, args, manager, symbols_allowed_long, symbols_allowed_short, True, False, False, False, False, False, True, True)

    for symbol in random_rotator_symbols:
        if len(open_position_symbols) >= symbols_allowed_long + symbols_allowed_short:
            logging.info("Maximum number of open positions reached.")
            break
        process_signal(symbol, args, manager, symbols_allowed_long, symbols_allowed_short, False, False, False, False, False, False, True, True)

    manage_excess_threads(symbols_allowed_long, symbols_allowed_short, symbols_allowed)
    time.sleep(5)

def manage_excess_threads(symbols_allowed_long, symbols_allowed_short, symbols_allowed):
    global active_symbols, active_long_symbols, active_short_symbols, unique_active_symbols

    with active_symbols_lock:
        while len(unique_active_symbols) > symbols_allowed:
            symbols_without_open_positions = unique_active_symbols - active_symbols
            if not symbols_without_open_positions:
                logging.warning("No symbols available to remove without affecting open positions.")
                break
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
    """
    Removes and cleans up a task for the given symbol from the executors.
    """
    global unique_active_symbols
    if symbol in long_threads:
        future, thread_completed = long_threads[symbol]
        action = "long"
    elif symbol in short_threads:
        future, thread_completed = short_threads[symbol]
        action = "short"
    else:
        return

    if future:
        # Attempt to cancel the future if it's still running
        cancelled = future.cancel()
        if not cancelled:
            logging.info(f"Cannot cancel {action} task for symbol {symbol} as it's already running.")
        else:
            logging.info(f"Cancelled {action} task for symbol {symbol}.")

    # Remove the future from tracking
    if symbol in long_threads:
        del long_threads[symbol]
    if symbol in short_threads:
        del short_threads[symbol]
    
    active_long_symbols.discard(symbol)
    active_short_symbols.discard(symbol)
    active_symbols.discard(symbol)
    unique_active_symbols.discard(symbol)
    logging.info(f"Cleaned up symbol {symbol} from active sets.")

def start_thread_for_open_symbol(symbol, args, manager, market_maker, mfirsi_signal, has_open_long, has_open_short,
                                 long_mode, short_mode, graceful_stop_long, graceful_stop_short, trading_executor):
    """
    Starts a thread to manage an open position (long or short) for a given symbol via ThreadPoolExecutor.
    """
    """
    Starts a thread to manage an open position (long or short) for a given symbol via ThreadPoolExecutor.
    """
    global unique_active_symbols, long_threads, short_threads, active_long_symbols, active_short_symbols, active_symbols

    action_taken = False
    if mfirsi_signal.lower() == "neutral":
        if has_open_long:
            thread_started = start_thread_for_symbol(
                symbol, args, manager, market_maker, mfirsi_signal,
                "manage_long", has_open_long, has_open_short,
                long_mode, short_mode,
                graceful_stop_long, graceful_stop_short,
                trading_executor
            )
            action_taken = action_taken or thread_started

        if has_open_short:
            thread_started = start_thread_for_symbol(
                symbol, args, manager, market_maker, mfirsi_signal,
                "manage_short", has_open_long, has_open_short,
                long_mode, short_mode,
                graceful_stop_long, graceful_stop_short,
                trading_executor
            )
            action_taken = action_taken or thread_started

    else:
        if long_mode and has_open_long and not graceful_stop_long:
            thread_started = start_thread_for_symbol(
                symbol, args, manager, market_maker, mfirsi_signal,
                "manage_long", has_open_long, has_open_short,
                long_mode, short_mode,
                graceful_stop_long, graceful_stop_short,
                trading_executor
            )
            action_taken = action_taken or thread_started

        if short_mode and has_open_short and not graceful_stop_short:
            thread_started = start_thread_for_symbol(
                symbol, args, manager, market_maker, mfirsi_signal,
                "manage_short", has_open_long, has_open_short,
                long_mode, short_mode,
                graceful_stop_long, graceful_stop_short,
                trading_executor
            )
            action_taken = action_taken or thread_started

    return action_taken

def start_thread_for_symbol(symbol, args, manager, market_maker, mfirsi_signal, action,
                            has_open_long, has_open_short, long_mode, short_mode,
                            graceful_stop_long, graceful_stop_short, trading_executor):
    """
    **UPDATED**: This function now creates a single threading.Event() object,
    passes it to `run_bot`, and also stores it in either `long_threads` or `short_threads`.
    """
    global unique_active_symbols, long_threads, short_threads, active_long_symbols, active_short_symbols, active_symbols
    global symbol_next_attempt_time

    # Define a cooldown period in seconds for the next attempt. This can match COOLDOWN_PERIOD in can_spawn_thread.
    COOLDOWN_PERIOD = 60
    current_time = time.time()

    # Early check: If we're still in cooldown, skip silently without logging attempts
    if symbol in symbol_next_attempt_time and current_time < symbol_next_attempt_time[symbol]:
        # Still in cooldown, do not log attempts or call can_spawn_thread. Just return.
        return False

    # Check cooldown for spawning thread
    if not can_spawn_thread(symbol):
        # If cooldown is triggered now, set next attempt time and return
        symbol_next_attempt_time[symbol] = current_time + COOLDOWN_PERIOD
        return False

    # If we reached here, we are allowed to attempt now.
    # Clear any scheduled attempt time since we're now attempting
    if symbol in symbol_next_attempt_time:
        del symbol_next_attempt_time[symbol]

    # Check if there's already a running task for this symbol/action
    if action == "manage_long" and symbol in long_threads and not long_threads[symbol][0].done():
        logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Long task already running for symbol {symbol}. Skipping.")
        return False
    elif action == "manage_short" and symbol in short_threads and not short_threads[symbol][0].done():
        logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Short task already running for symbol {symbol}. Skipping.")
        return False

    # **UPDATED**: We create a single event for this thread
    thread_completed_event = threading.Event()

    future = trading_executor.submit(
        run_bot,
        symbol,
        args,
        market_maker,
        manager,
        args.account_name,
        manager.symbols_allowed_long,
        manager.symbols_allowed_short,
        latest_rotator_symbols,
        thread_completed_event,  # <-- same object we store below
        mfirsi_signal,
        action,
        trading_executor
    )

    # Now store (future, same_event) in the dictionary
    if action == "manage_long":
        long_threads[symbol] = (future, thread_completed_event)
        active_long_symbols.add(symbol)
    elif action == "manage_short":
        short_threads[symbol] = (future, thread_completed_event)
        active_short_symbols.add(symbol)

    active_symbols.add(symbol)
    unique_active_symbols.add(symbol)
    logging.info(f"(func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Submitted run_bot task for symbol {symbol} with action {action}.")
    return True

def fetch_updated_symbols(args, manager, config, whitelist=None):
    current_time = time.time()
    if current_time - rotator_symbols_cache['timestamp'] < CACHE_DURATION:
        logging.info("Using cached rotator symbols")
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
            potential_bullish_symbols = manager.get_bullish_rotator_symbols(None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
            potential_bearish_symbols = manager.get_bearish_rotator_symbols(None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
            potential_symbols = potential_bullish_symbols + potential_bearish_symbols
        elif strategy == 'basicgridmfirsi':
            potential_bullish_symbols = manager.get_bullish_rotator_symbols(None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
            potential_bearish_symbols = manager.get_bearish_rotator_symbols(None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
            potential_symbols = potential_bullish_symbols + potential_bearish_symbols
        elif strategy == 'qstrendlongonly':
            potential_symbols = manager.get_bullish_rotator_symbols(None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
        elif strategy == 'qstrendshortonly':
            potential_symbols = manager.get_bearish_rotator_symbols(None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)
        else:
            potential_symbols = manager.get_auto_rotate_symbols(None, blacklist=blacklist, whitelist=whitelist, max_usd_value=max_usd_value)

    # Limit to 10 symbols
    potential_symbols = potential_symbols[:10]  # Limit to the first 10 symbols

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
