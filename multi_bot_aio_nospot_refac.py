# multi_bot_aio_nospot.py

import sys
import os
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from concurrent.futures import Future
import threading
from threading import Thread
import inspect
import random
import colorama
from colorama import Fore, Back, Style, init
from pathlib import Path

project_dir = str(Path(__file__).resolve().parent)
print("Project directory:", project_dir)
sys.path.insert(0, project_dir)

import traceback

from rich.live import Live
import argparse
from pathlib import Path
from config import load_config, Config, VERSION
from api.manager import Manager

from directionalscalper.core.exchanges import *

import directionalscalper.core.strategies.bybit.gridbased as gridbased
import directionalscalper.core.strategies.bybit.hedging as bybit_hedging
from directionalscalper.core.strategies.binance import *
from directionalscalper.core.strategies.huobi import *

from live_table_manager import LiveTableManager, shared_symbols_data

from directionalscalper.core.strategies.logger import Logger

from rate_limit import RateLimit

from collections import deque

# COMMENT: These rate limiters are used as context managers to throttle
# how often certain API calls are made.
general_rate_limiter = RateLimit(50, 1)
order_rate_limiter = RateLimit(5, 1) 

# COMMENT: thread_management_lock is our single concurrency lock used to protect
# updates to shared data structures like active_symbols, unique_active_symbols, etc.
thread_management_lock = threading.Lock()

# COMMENT: thread_to_symbol tracks which thread is responsible for which symbol.
# It's a dictionary from Thread object -> symbol.
thread_to_symbol = {}

# We no longer use thread_to_symbol_lock; we rely on a single lock (thread_management_lock).
# thread_to_symbol_lock = threading.Lock()

# COMMENT: Sets that track the current state of active or open trades.
active_symbols = set()
active_threads = []
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


logging = Logger(logger_name="MultiBot", filename="MultiBot.log", stream=True)

colorama.init()

def print_cool_trading_info(symbol, exchange_name, strategy_name, account_name):
    """
    COMMENT: Just prints a fancy banner and some metadata about
    the strategy, exchange, symbol, etc.
    """
    ascii_art = r"""
    ____  _               _   _                   _  ____            _                
   |  _ \(_)_ __ ___  ___| |_(_) ___  _ __   __ _| |/ ___|  ___ __ _| |_ __   ___ _ __ 
   | | | | | '__/ _ \/ __| __| |/ _ \| '_ \ / _` | |\___ \ / __/ _` | | '_ \ / _ \ '__|
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
    """
    COMMENT: A small utility that normalizes a symbol by removing slashes and colons.
    For instance, 'BTC/USDT:USDT' -> 'BTC'
    """
    return symbol.replace('/', '').split(':')[0]

def get_available_strategies():
    return [
        'qsgridob'
    ]

def choose_strategy():
    """
    COMMENT: Asks the user to pick a strategy from a list using inquirer.
    """
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
    """
    COMMENT: If the user hasn't provided exchange, strategy, or account name,
    this function interacts with them via inquirer to fill in missing info.
    """
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
    """
    COMMENT: This class sets up the exchange object, pulling in configuration from
    config.exchanges. It's also responsible for deciding which signal approach to use
    (like 'lorentzian' vs 'mfirsi_signal'), and running the selected strategy.
    """
    def __init__(self, config: Config, exchange_name: str, account_name: str):
        self.config = config
        self.exchange_name = exchange_name
        self.account_name = account_name
        # The strategy's "entry signal type" is read from config, defaults to 'lorentzian'
        self.entry_signal_type = config.bot.linear_grid.get('entry_signal_type', 'lorentzian')
        self.strategy = None  # Initialize strategy attribute as None

        exchange_config = next((exch for exch in config.exchanges
                                if exch.name == exchange_name and exch.account_name == account_name), None)
        
        if not exchange_config:
            raise ValueError(f"Exchange {exchange_name} with account {account_name} not found in the configuration file.")

        api_key = exchange_config.api_key
        secret_key = exchange_config.api_secret
        passphrase = getattr(exchange_config, 'passphrase', None)  # Use getattr to get passphrase if it exists
        
        exchange_classes = {
            'bybit': BybitExchange
        }

        exchange_class = exchange_classes.get(exchange_name.lower(), Exchange)

        # COMMENT: Initialize the chosen Exchange class with the correct keys.
        # Some require passphrase, others do not.
        if exchange_name.lower() in ['bybit', 'binance']:
            self.exchange = exchange_class(api_key, secret_key)
        else:
            self.exchange = exchange_class(api_key, secret_key, passphrase)

    def run_strategy(self, symbol, strategy_name, config, account_name,
                    symbols_to_trade=None, rotator_symbols_standardized=None,
                    mfirsi_signal=None, action=None, thread_id=None):
        """
        COMMENT: This is called (e.g. by run_bot) once we have a signal to open a position.
        It picks the correct class in 'strategy_classes', instantiates it, and calls .run(...).
        """
        logging.info(f"[Thread-{thread_id}] [[{symbol}]] Received rotator symbols in run_strategy...")
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Received rotator symbols in run_strategy ({strategy_name}) for {symbol} ({len(rotator_symbols_standardized)}): {list(rotator_symbols_standardized)[:5]}...")
        
        exchange_config = next((exch for exch in config.exchanges
                                if exch.name == self.exchange_name and exch.account_name == account_name), None)
        
        if not exchange_config:
            raise ValueError(f"Exchange {self.exchange_name} with account {account_name} not found in the configuration file.")

        # Use getattr with default values
        symbols_allowed = getattr(exchange_config, 'symbols_allowed', 10)
        symbols_allowed_long = getattr(exchange_config, 'symbols_allowed_long', symbols_allowed)
        symbols_allowed_short = getattr(exchange_config, 'symbols_allowed_short', symbols_allowed)

        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Matched exchange: {self.exchange_name}, account: {account_name}. symbols_allowed: {symbols_allowed}")
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Matched exchange: {self.exchange_name}, account: {account_name}. symbols_allowed_long: {symbols_allowed_long}")
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Matched exchange: {self.exchange_name}, account: {account_name}. symbols_allowed_short: {symbols_allowed_short}")

        if symbols_to_trade:
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Calling run method with symbols: {symbols_to_trade}")
            try:
                print_cool_trading_info(symbol, self.exchange_name, strategy_name, account_name)
                logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Printed trading info for {symbol}")
            except Exception as e:
                logging.error(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Error in printing info: {e}")

        strategy_classes = {
            'qstrendobdynamictp': gridbased.BybitQuickScalpTrendDynamicTP,
            'qsgridob': gridbased.LinearGridBaseFutures
        }

        strategy_class = strategy_classes.get(strategy_name.lower())
        if strategy_class:
            # Store the strategy instance
            self.strategy = strategy_class(self.exchange, self.manager, config.bot, symbols_allowed)
            try:
                logging.info(f"[Thread-{thread_id}] [[{symbol}]] (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Running strategy for symbol {symbol} with action {action}")
                if action == "long":
                    future_long = Future()
                    Thread(target=self.run_with_future, args=(self.strategy, symbol, rotator_symbols_standardized, mfirsi_signal, "long", future_long)).start()
                    return future_long
                elif action == "short":
                    future_short = Future()
                    Thread(target=self.run_with_future, args=(self.strategy, symbol, rotator_symbols_standardized, mfirsi_signal, "short", future_short)).start()
                    return future_short
                else:
                    # If no action is specified, we simply create a Future with a success result.
                    future = Future()
                    future.set_result(True)
                    return future
            except Exception as e:
                future = Future()
                future.set_exception(e)
                return future
        else:
            logging.error(f"[Thread-{thread_id}] [[{symbol}]] (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Strategy {strategy_name} not found.")
            future = Future()
            future.set_exception(ValueError(f"Strategy {strategy_name} not found."))
            return future

    def run_with_future(self, strategy, symbol, rotator_symbols_standardized,
                        mfirsi_signal, action, future):
        """
        COMMENT: This helper is used to wrap strategy.run(...) calls in a thread,
        so that the actual run can be awaited with a Future.
        """
        try:
            strategy.run(symbol,
                         rotator_symbols_standardized=rotator_symbols_standardized,
                         mfirsi_signal=mfirsi_signal,
                         action=action)
            future.set_result(True)
        except Exception as e:
            future.set_exception(e)

    # COMMENT: The below methods fetch balances, create orders, etc.
    # We'll skip repeating commentary for them since they are straightforward.
    def get_balance(self, quote, market_type=None, sub_type=None):
        if self.exchange_name == 'bitget':
            return self.exchange.get_balance_bitget(quote)
        elif self.exchange_name == 'bybit':
            #self.exchange.retry_api_call(self.exchange.get_balance_bybit, quote)
            # return self.exchange.retry_api_call(self.exchange.get_balance_bybit(quote))
            return self.exchange.get_balance_bybit(quote)
        elif self.exchange_name == 'bybit_unified':
            return self.exchange.retry_api_call(self.exchange.get_balance_bybit(quote))

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
        """
        COMMENT: This chooses which type of signal to fetch based on 'entry_signal_type'.
        Typically returns 'long', 'short', or 'neutral'.
        """
        if self.entry_signal_type == 'mfirsi_signal':
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Using mfirsi signals for symbol {symbol}")
            signal = self.get_mfirsi_signal(symbol)
        elif self.entry_signal_type == 'lorentzian':
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Using lorentzian signals for symbol {symbol}")
            signal = self.generate_l_signals(symbol)
        else:
            raise ValueError(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Unknown entry signal type: {self.entry_signal_type}")

        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Generated signal for {symbol}: {signal}")
        if signal == "neutral":
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Skipping processing for {symbol} due to neutral signal.")
            return "neutral"  # Return a specific flag for neutral signals
        return signal

    def generate_l_signals(self, symbol):
        with general_rate_limiter:
            return self.exchange.generate_l_signals(symbol)

    def get_mfirsi_signal(self, symbol):
        # Retrieve the MFI/RSI signal
        with general_rate_limiter:
            return self.exchange.get_mfirsi_ema_secondary_ema(symbol, limit=100, lookback=1, ema_period=5, secondary_ema_period=3)

BALANCE_REFRESH_INTERVAL = 600  # in seconds

orders_canceled = False

def run_bot(symbol, args, market_maker, manager, account_name,
            symbols_allowed, rotator_symbols_standardized,
            thread_completed, mfirsi_signal, action):
    """
    COMMENT: This function is the 'main' method for a single symbol's trading thread.
    It's launched typically by start_thread_for_symbol or start_thread_for_open_symbol
    once we have a signal for that symbol. It:
      - loads config
      - checks if we have capacity
      - sets up a 'finally' block to remove symbol from sets when done
      - calls market_maker.run_strategy(...)
    """
    global orders_canceled, unique_active_symbols, active_long_symbols, active_short_symbols
    current_thread = threading.current_thread()
    thread_id = current_thread.ident  # Get unique thread identifier

    # Define a unique identifier for action
    action_id = action  # Action is already unique for the thread, so we use it directly.
    
    # def thread_log(message):
    #     """Helper function for thread-specific logging"""
    #     logging.info(f"[Thread-{thread_id}] (caller: {inspect.stack()[1].function}, "
    #                 f"func: {inspect.currentframe().f_code.co_name}, "
    #                 f"line: {inspect.currentframe().f_lineno}) [[{symbol}]] {message}")
    
    logging.info(f"[Thread-{thread_id}] [[{symbol}]] Starting run_bot for {symbol} with action {action}.")
    try:
        if not args.config.startswith('configs/'):
            config_file_path = Path('configs/' + args.config)
        else:
            config_file_path = Path(args.config)

        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Loading config from: {config_file_path}")

        account_file_path = Path('configs/account.json')
        config = load_config(config_file_path, account_file_path)

        exchange_name = args.exchange
        strategy_name = args.strategy
        account_name = args.account_name

        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Trading symbol: {symbol}")
        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Exchange name: {exchange_name}")
        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Strategy name: {strategy_name}")
        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Account name: {account_name}")

        # COMMENT: The manager is the entity that communicates with the exchange and
        # can also fetch signals, data, etc.
        market_maker.manager = manager

        # COMMENT: We'll define a small helper function to fetch open positions from the exchange
        def fetch_open_positions():
            with general_rate_limiter:
                return getattr(manager.exchange, f"get_all_open_positions_{args.exchange.lower()}")()

        open_position_data = fetch_open_positions()
        open_position_symbols = {standardize_symbol(pos['symbol']) for pos in open_position_data}
        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Open position symbols: {open_position_symbols}")

        current_long_positions = [standardize_symbol(pos['symbol']) for pos in open_position_data if pos['side'].lower() == 'long']
        current_short_positions = [standardize_symbol(pos['symbol']) for pos in open_position_data if pos['side'].lower() == 'short']

        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Current long positions: {current_long_positions}")
        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Current short positions: {current_short_positions}")

        # COMMENT: We acquire thread_management_lock to update shared sets
        with thread_management_lock:
            is_open_position = symbol in open_position_symbols
            # If not already open, check if we can add it
            if not is_open_position and len(unique_active_symbols) >= symbols_allowed and symbol not in unique_active_symbols:
                logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Symbols allowed limit reached. Skipping new symbol {symbol}.")
                return

            # If we have capacity, we proceed and register the symbol in sets:
            thread_to_symbol[current_thread] = symbol
            active_symbols.add(symbol)
            unique_active_symbols.add(symbol)
            if action == "long" or symbol in current_long_positions:
                active_long_symbols.add(symbol)
            elif action == "short" or symbol in current_short_positions:
                active_short_symbols.add(symbol)

        # COMMENT: In the first run, we optionally cancel all open orders on Bybit (once only).
        try:
            if not orders_canceled and hasattr(market_maker.exchange, 'cancel_all_open_orders_bybit'):
                market_maker.exchange.cancel_all_open_orders_bybit()
                logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Cleared all open orders on the exchange upon initialization.")
                orders_canceled = True
        except Exception as e:
            logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Exception caught while cancelling orders: {e}")

        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Rotator symbols in run_bot: ({len(rotator_symbols_standardized)}): {list(rotator_symbols_standardized)[:5]}...")
        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Latest rotator symbols in run bot ({len(latest_rotator_symbols)}): {list(latest_rotator_symbols)[:5]}...")

        # COMMENT: Sleep to avoid spamming the API too quickly right after the thread starts.
        time.sleep(2)

        # COMMENT: We get the signal for the symbol (though we often already have it),
        # then call run_strategy to place orders, etc.
        with general_rate_limiter:
            signal = market_maker.get_signal(symbol)
            logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Retrieved signal for {symbol}: {signal}")
            future = market_maker.run_strategy(
                symbol, 
                args.strategy, 
                config, 
                account_name, 
                symbols_to_trade=symbols_allowed, 
                rotator_symbols_standardized=latest_rotator_symbols, 
                mfirsi_signal=signal, 
                action=action,
                thread_id=thread_id  # Pass thread ID to strategy
            )
            future.result()

        logging.info(f"[Thread-{thread_id}] [[{symbol}]] Successfully ran strategy.")
    except Exception as e:
        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) An error occurred in run_bot for symbol {symbol}: {e}")
        logging.error(traceback.format_exc())
    finally:
        # COMMENT: Once we finish or crash out, we remove the symbol from the sets
        # so the system knows this thread is done with the symbol.
        with thread_management_lock:
            if current_thread in thread_to_symbol:
                del thread_to_symbol[current_thread]
            active_symbols.discard(symbol)
            unique_active_symbols.discard(symbol)
            active_long_symbols.discard(symbol)
            active_short_symbols.discard(symbol)
        logging.info(f"[Thread-{thread_id}] [[{symbol}]] (Action-{action_id}) (caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name},line: {inspect.currentframe().f_lineno}) Thread for symbol {symbol} with action {action} has completed.")
        thread_completed.set()

def bybit_auto_rotation(args, market_maker, manager, symbols_allowed, symbols_allowed_long, symbols_allowed_short):
    """
    COMMENT: This is the main loop for auto-rotating symbols on Bybit (derivatives).
    It creates two thread pools:
      1) signal_executor -> to handle signal processing tasks
      2) trading_executor -> to handle actual trade threads
    Then it repeatedly fetches open positions, updates the set of open symbols,
    fetches new rotator symbols, decides which tasks to schedule, etc.
    """
    global latest_rotator_symbols, long_threads, short_threads
    global active_symbols, active_long_symbols, active_short_symbols
    global last_rotator_update_time, unique_active_symbols

    max_workers_signals = 2
    max_workers_trading = 2

    # COMMENT: Two separate pools, each with 1 worker.
    signal_executor = ThreadPoolExecutor(max_workers=max_workers_signals)
    trading_executor = ThreadPoolExecutor(max_workers=max_workers_trading)

    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Initialized signal executor with max workers: {max_workers_signals}")
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Initialized trading executor with max workers: {max_workers_trading}")

    config_file_path = Path('configs/' + args.config) if not args.config.startswith('configs/') else Path(args.config)
    account_file_path = Path('configs/account.json')
    config = load_config(config_file_path, account_file_path)

    # COMMENT: The manager is attached to the market_maker so it can do certain tasks.
    market_maker.manager = manager

    long_mode = config.bot.linear_grid['long_mode']
    short_mode = config.bot.linear_grid['short_mode']
    config_graceful_stop_long = config.bot.linear_grid.get('graceful_stop_long', False)
    config_graceful_stop_short = config.bot.linear_grid.get('graceful_stop_short', False)
    config_auto_graceful_stop = config.bot.linear_grid.get('auto_graceful_stop', False)
    target_coins_mode = config.bot.linear_grid.get('target_coins_mode', False)
    whitelist = set(config.bot.whitelist) if target_coins_mode else None

    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Target coins mode is {'enabled' if target_coins_mode else 'disabled'}")

    def fetch_open_positions():
        with general_rate_limiter:
            return getattr(manager.exchange, f"get_all_open_positions_{args.exchange.lower()}")()

    open_position_data = fetch_open_positions()
    current_long_positions = sum(1 for pos in open_position_data if pos['side'].lower() == 'long')
    current_short_positions = sum(1 for pos in open_position_data if pos['side'].lower() == 'short')

    # COMMENT: "graceful_stop_long"/"graceful_stop_short" are flags that, if true,
    # means we won't open new positions of that type.
    graceful_stop_long = current_long_positions >= symbols_allowed or config_graceful_stop_long
    graceful_stop_short = current_short_positions >= symbols_allowed or config_graceful_stop_short

    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Long mode: {long_mode}")
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Short mode: {short_mode}")
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Initial Graceful stop long: {graceful_stop_long}")
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Initial Graceful stop short: {graceful_stop_short}")
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Auto graceful stop: {config_auto_graceful_stop}")

    def process_futures(futures):
        """
        COMMENT: This helper waits for all the futures in a list to complete
        (as_completed) and logs any exceptions.
        """
        for future in as_completed(futures):
            try:
                future.result()
            except Exception as e:
                logging.error(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Exception in thread: {e}")
                logging.debug(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno})", traceback.format_exc())

    processed_symbols = set()

    loop_counter = 0
    while True:
        loop_counter += 1
        logging.info(f"(loop #{loop_counter}) Starting loop iteration.")

        try:
            current_time = time.time()
            open_position_data = fetch_open_positions()
            open_position_symbols = {standardize_symbol(pos['symbol']) for pos in open_position_data}
            logging.info(f"(loop #{loop_counter}) Open position symbols: {open_position_symbols}")

            current_long_positions = sum(1 for pos in open_position_data if pos['side'].lower() == 'long')
            current_short_positions = sum(1 for pos in open_position_data if pos['side'].lower() == 'short')
            logging.info(f"(loop #{loop_counter}) Current long positions: {current_long_positions}, Current short positions: {current_short_positions}")

            update_active_symbols(open_position_symbols)
            unique_active_symbols = active_long_symbols.union(active_short_symbols)

            if config_auto_graceful_stop:
                if (current_long_positions >= symbols_allowed or len(unique_active_symbols) >= symbols_allowed) and not graceful_stop_long:
                    graceful_stop_long = True
                    logging.info(f"(loop #{loop_counter}) GS Auto Check: Automatically enabled graceful stop for long.")
                elif current_long_positions < symbols_allowed and len(unique_active_symbols) < symbols_allowed and graceful_stop_long:
                    graceful_stop_long = config_graceful_stop_long
                    logging.info(f"(loop #{loop_counter}) GS Auto Check: Reverted graceful stop long to config value.")
                else:
                    logging.info(f"(loop #{loop_counter}) GS Auto Check: Current long positions: {current_long_positions}, graceful_stop_long: {graceful_stop_long}")

                if (current_short_positions >= symbols_allowed or len(unique_active_symbols) >= symbols_allowed) and not graceful_stop_short:
                    graceful_stop_short = True
                    logging.info(f"(loop #{loop_counter}) GS Auto Check: Automatically enabled graceful stop for short.")
                elif current_short_positions < symbols_allowed and len(unique_active_symbols) < symbols_allowed and graceful_stop_short:
                    graceful_stop_short = config_graceful_stop_short
                    logging.info(f"(loop #{loop_counter}) GS Auto Check: Reverted graceful stop short to config value.")
                else:
                    logging.info(f"(loop #{loop_counter}) GS Auto Check: Current short positions: {current_short_positions}, graceful_stop_short: {graceful_stop_short}")

            if not latest_rotator_symbols or current_time - last_rotator_update_time >= 60:
                with general_rate_limiter:
                    latest_rotator_symbols = fetch_updated_symbols(args, manager, whitelist)
                last_rotator_update_time = current_time
                processed_symbols.clear()
                symbols_to_log = list(latest_rotator_symbols)[:5]
                logging.info(f"(loop #{loop_counter}) Refreshed latest rotator symbols: {symbols_to_log}...")
            else:
                logging.debug(f"(loop #{loop_counter}) No refresh needed yet. Last update was at {last_rotator_update_time}.")

            with thread_management_lock:
                open_position_futures = []
                signal_futures = []

                # Update sets again inside lock, then see what's active
                update_active_symbols(open_position_symbols)
                unique_active_symbols = active_long_symbols.union(active_short_symbols)

                logging.info(f"(loop #{loop_counter}) Active long symbols ({len(active_long_symbols)}): {active_long_symbols}")
                logging.info(f"(loop #{loop_counter}) Active short symbols ({len(active_short_symbols)}): {active_short_symbols}")
                logging.info(f"(loop #{loop_counter}) unique_active_symbols ({len(unique_active_symbols)}): {unique_active_symbols}")
                logging.info(f"(loop #{loop_counter}) trading_executor queue size: {trading_executor._work_queue.qsize() if hasattr(trading_executor, '_work_queue') else 'N/A'}")
                logging.info(f"(loop #{loop_counter}) signal_executor queue size: {signal_executor._work_queue.qsize() if hasattr(signal_executor, '_work_queue') else 'N/A'}")

                # ---------------------------------------------------------
                # PART 1: For each symbol that truly has an open position
                # ---------------------------------------------------------
                for symbol in open_position_symbols.copy():
                    has_open_long = any(
                        pos['side'].lower() == 'long'
                        and standardize_symbol(pos['symbol']) == symbol
                        for pos in open_position_data
                    )
                    has_open_short = any(
                        pos['side'].lower() == 'short'
                        and standardize_symbol(pos['symbol']) == symbol
                        for pos in open_position_data
                    )

                    # Always submit the "signal check" for open positions
                    open_position_futures.append(
                        signal_executor.submit(
                            process_signal_for_open_position,
                            symbol,
                            args, market_maker, manager,
                            symbols_allowed, symbols_allowed_long, symbols_allowed_short,
                            open_position_data,
                            long_mode, short_mode,
                            graceful_stop_long, graceful_stop_short
                        )
                    )

                    # -----------------------
                    # (A) Checking LONG side
                    # -----------------------
                    if has_open_long:
                        existing_long_entry = long_threads.get(symbol)
                        if existing_long_entry:
                            thread_obj, thread_completed_evt = existing_long_entry
                            still_alive = thread_obj.is_alive()
                            already_done = thread_completed_evt.is_set()
                            if still_alive or not already_done:
                                thread_id = thread_obj.ident if thread_obj.ident else "Unknown"
                                logging.info(
                                    f"(loop #{loop_counter}) Skipping re-submission of LONG thread for {symbol}, "
                                    f"previous thread (ID: {thread_id}) is still running or not cleaned up."
                                )
                            else:
                                # Old thread is done => remove from dict
                                del long_threads[symbol]
                                # Now we can safely submit a new thread if needed:
                                open_position_futures.append(
                                    trading_executor.submit(
                                        start_thread_for_open_symbol,
                                        symbol,
                                        args, 
                                        manager,
                                        "long",
                                        has_open_long=True,
                                        has_open_short=False,
                                        long_mode=long_mode,
                                        short_mode=short_mode,
                                        graceful_stop_long=graceful_stop_long,
                                        graceful_stop_short=graceful_stop_short,
                                        symbols_allowed=symbols_allowed,
                                        symbols_allowed_long=symbols_allowed_long,
                                        symbols_allowed_short=symbols_allowed_short
                                    )
                                )
                                active_long_symbols.add(symbol)
                                unique_active_symbols.add(symbol)
                                logging.info(f"(loop #{loop_counter}) Submitted long thread for open symbol {symbol}.")
                                time.sleep(2)
                        else:
                            # No previous record => brand-new thread
                            open_position_futures.append(
                                trading_executor.submit(
                                    start_thread_for_open_symbol,
                                    symbol,
                                    args, manager,
                                    "long",
                                    has_open_long=True,
                                    has_open_short=False,
                                    long_mode=long_mode,
                                    short_mode=short_mode,
                                    graceful_stop_long=graceful_stop_long,
                                    graceful_stop_short=graceful_stop_short,
                                    symbols_allowed=symbols_allowed,
                                    symbols_allowed_long=symbols_allowed_long,
                                    symbols_allowed_short=symbols_allowed_short
                                )
                            )
                            active_long_symbols.add(symbol)
                            unique_active_symbols.add(symbol)
                            logging.info(f"(loop #{loop_counter}) Submitted long thread for open symbol {symbol}.")
                            time.sleep(2)

                    # ------------------------
                    # (B) Checking SHORT side
                    # ------------------------
                    if has_open_short:
                        existing_short_entry = short_threads.get(symbol)
                        if existing_short_entry:
                            thread_obj, thread_completed_evt = existing_short_entry
                            still_alive = thread_obj.is_alive()
                            already_done = thread_completed_evt.is_set()
                            if still_alive or not already_done:
                                thread_id = thread_obj.ident if thread_obj.ident else "Unknown"
                                logging.info(
                                    f"(loop #{loop_counter}) Skipping re-submission of SHORT thread for {symbol}, "
                                    f"previous thread (ID: {thread_id}) is still running or not cleaned up."
                                )
                            else:
                                # Old thread is done => remove from dict
                                del short_threads[symbol]
                                # Now we can safely submit a new thread if needed:
                                open_position_futures.append(
                                    trading_executor.submit(
                                        start_thread_for_open_symbol,
                                        symbol,
                                        args, manager,
                                        "short",
                                        has_open_long=False,
                                        has_open_short=True,
                                        long_mode=long_mode,
                                        short_mode=short_mode,
                                        graceful_stop_long=graceful_stop_long,
                                        graceful_stop_short=graceful_stop_short,
                                        symbols_allowed=symbols_allowed,
                                        symbols_allowed_long=symbols_allowed_long,
                                        symbols_allowed_short=symbols_allowed_short
                                    )
                                )
                                active_short_symbols.add(symbol)
                                unique_active_symbols.add(symbol)
                                logging.info(f"(loop #{loop_counter}) Submitted short thread for open symbol {symbol}.")
                                time.sleep(2)
                        else:
                            # No previous record => brand-new thread
                            open_position_futures.append(
                                trading_executor.submit(
                                    start_thread_for_open_symbol,
                                    symbol,
                                    args, manager,
                                    "short",
                                    has_open_long=False,
                                    has_open_short=True,
                                    long_mode=long_mode,
                                    short_mode=short_mode,
                                    graceful_stop_long=graceful_stop_long,
                                    graceful_stop_short=graceful_stop_short,
                                    symbols_allowed=symbols_allowed,
                                    symbols_allowed_long=symbols_allowed_long,
                                    symbols_allowed_short=symbols_allowed_short
                                )
                            )
                            active_short_symbols.add(symbol)
                            unique_active_symbols.add(symbol)
                            logging.info(f"(loop #{loop_counter}) Submitted short thread for open symbol {symbol}.")
                            time.sleep(2)

                # ---------------------------------------------------------
                # PART 2: For new (non-open) symbols if capacity remains
                # ---------------------------------------------------------
                if len(unique_active_symbols) < symbols_allowed:
                    symbols_to_process = whitelist if target_coins_mode else latest_rotator_symbols
                    logging.info(f"(loop #{loop_counter}) unique_active_symbols below limit. Checking new symbols.")
                    for symbol in symbols_to_process:
                        if symbol not in processed_symbols and symbol not in unique_active_symbols:
                            if len(unique_active_symbols) >= symbols_allowed:
                                logging.info(f"(loop #{loop_counter}) Reached symbols_allowed limit. Stopping new symbols.")
                                break
                            # can_open_long = len(active_long_symbols) < symbols_allowed and not graceful_stop_long
                            # can_open_short = len(active_short_symbols) < symbols_allowed and not graceful_stop_short
                            can_open_long = (len(active_long_symbols) < symbols_allowed_long) and (len(unique_active_symbols) < symbols_allowed) and not graceful_stop_long
                            can_open_short = (len(active_short_symbols) < symbols_allowed_short) and (len(unique_active_symbols) < symbols_allowed) and not graceful_stop_short

                            if (can_open_long and long_mode) or (can_open_short and short_mode):
                                signal_futures.append(
                                    signal_executor.submit(
                                        process_signal,
                                        symbol,
                                        args, market_maker, manager,
                                        symbols_allowed, symbols_allowed_long, symbols_allowed_short, open_position_data,
                                        False,
                                        can_open_long, can_open_short,
                                        graceful_stop_long, graceful_stop_short
                                    )
                                )
                                logging.info(f"(loop #{loop_counter}) Submitted signal processing for new symbol {symbol}.")
                                processed_symbols.add(symbol)
                                unique_active_symbols.add(symbol)
                                time.sleep(2)

                logging.info(f"(loop #{loop_counter}) Submitted signal processing for open position symbols: {open_position_symbols}.")
                process_futures(open_position_futures + signal_futures)

                # ---------------------------------------------------------
                # PART 3: Cleanup for completed threads
                # ---------------------------------------------------------
                completed_symbols = []
                all_threads = {**long_threads, **short_threads}  # merge dicts
                for sym, (thread, thread_completed) in all_threads.items():
                    if thread_completed.is_set():
                        thread.join()  # ensure it’s fully finished
                        completed_symbols.append(sym)

                for sym in completed_symbols:
                    active_symbols.discard(sym)
                    if sym in long_threads:
                        del long_threads[sym]
                    if sym in short_threads:
                        del short_threads[sym]
                    active_long_symbols.discard(sym)
                    active_short_symbols.discard(sym)
                    unique_active_symbols.discard(sym)
                    logging.info(f"(loop #{loop_counter}) Cleaned up completed symbol {sym}.")

        except Exception as e:
            logging.error(f"(loop #{loop_counter}) Exception in bybit_auto_rotation: {str(e)}")
            logging.debug(f"(loop #{loop_counter}) Traceback: {traceback.format_exc()}")

        time.sleep(1)

def process_signal_for_open_position(
    symbol,
    args,
    market_maker,
    manager,
    symbols_allowed,
    symbols_allowed_long,
    symbols_allowed_short,
    open_position_data,
    long_mode,
    short_mode,
    graceful_stop_long,
    graceful_stop_short
):
    try:
        market_maker.manager = manager

        # Initialize the strategy if not already initialized
        if market_maker.strategy is None:
            config_file_path = (
                Path('configs/' + args.config)
                if not args.config.startswith('configs/')
                else Path(args.config)
            )
            account_file_path = Path('configs/account.json')
            config = load_config(config_file_path, account_file_path)

            strategy_classes = {
                'qstrendobdynamictp': gridbased.BybitQuickScalpTrendDynamicTP,
                'qsgridob': gridbased.LinearGridBaseFutures
            }

            strategy_class = strategy_classes.get(args.strategy.lower())
            if strategy_class:
                market_maker.strategy = strategy_class(
                    market_maker.exchange,
                    market_maker.manager,
                    config.bot,
                    symbols_allowed
                )
            else:
                logging.error(f"[[{symbol}]] Unknown strategy: {args.strategy}")
                return False

        # Check if grid creation should be attempted
        if hasattr(market_maker, 'strategy') and market_maker.strategy is not None:
            if not market_maker.strategy.should_attempt_grid_creation(symbol):
                logging.info(
                    f"[[{symbol}]] Skipping grid creation, symbol in cooldown period or position exceeding limits"
                )
                return False
        else:
            logging.error(f"[[{symbol}]] Strategy not properly initialized")
            return False

        # Acquire rate limiter and get the current signal
        with general_rate_limiter:
            signal = market_maker.get_signal(symbol)

        # If the signal is neutral, revert to the current position's direction
        if signal == "neutral":
            # Handle open_position_data as a list
            if isinstance(open_position_data, list) and len(open_position_data) > 0:
                # Assuming the first element represents the current position
                current_position = open_position_data[0]
                
                # Log the entire current_position for inspection
                logging.debug(
                    f"[[{symbol}]] Current position data: {current_position}"
                )

                # Attempt to extract 'side' from the 'info' dictionary
                info = current_position.get('info', {})
                position_side_raw = info.get('side', '').lower()

                # Define mapping from various descriptors to 'long' or 'short'
                position_mapping = {
                    'buy': 'long',
                    'sell': 'short',
                    'long': 'long',
                    'short': 'short'
                }

                # Apply mapping if necessary
                mapped_position_type = position_mapping.get(position_side_raw, position_side_raw)

                if mapped_position_type in ['long', 'short']:
                    logging.info(
                        f"[[{symbol}]] Neutral signal received. Reverting to current position type: {mapped_position_type}"
                    )
                    signal = mapped_position_type
                else:
                    logging.error(
                        f"[[{symbol}]] Neutral signal received but position type is unknown: '{position_side_raw}'. Current position data: {current_position}"
                    )
                    return False
            else:
                logging.error(
                    f"[[{symbol}]] Neutral signal received but no open position data available or data is not a list."
                )
                return False

        logging.info(
            f"[[{symbol}]] Processing signal for open position symbol {symbol}. Signal: {signal}"
        )

        # Call handle_signal with the determined signal
        action_taken = handle_signal(
            symbol,
            args,
            manager,
            signal,
            open_position_data,
            symbols_allowed,
            symbols_allowed_long,
            symbols_allowed_short,
            True,
            long_mode,
            short_mode,
            graceful_stop_long,
            graceful_stop_short
        )

        if action_taken:
            logging.info(f"[[{symbol}]] Action taken for open position symbol {symbol}.")
        else:
            logging.info(f"[[{symbol}]] No action taken for open position symbol {symbol}.")

        return action_taken

    except Exception as e:
        logging.debug(
            f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) "
            f"Exception occurred: {e}\n{traceback.format_exc()}"
        )
        return False

def process_signal(symbol, args, market_maker, manager, symbols_allowed, symbols_allowed_long, symbols_allowed_short, open_position_data, is_open_position, long_mode, short_mode, graceful_stop_long, graceful_stop_short):
    market_maker.manager = manager
    signal = market_maker.get_signal(symbol)  # Use the appropriate signal based on the entry_signal_type

    if signal == "neutral":  # Check for neutral signal
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Skipping signal processing for {symbol} due to neutral signal.")
        return False

    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Processing signal for {'open position' if is_open_position else 'new rotator'} symbol {symbol}. Signal: {signal}")

    action_taken = handle_signal(symbol, args, manager, signal, open_position_data, symbols_allowed, symbols_allowed_long, symbols_allowed_short, is_open_position, long_mode, short_mode, graceful_stop_long, graceful_stop_short)

    if action_taken:
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Action taken for {'open position' if is_open_position else 'new rotator'} symbol {symbol}.")
    else:
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] No action taken for {'open position' if is_open_position else 'new rotator'} symbol {symbol} due to existing position or lack of clear signal.")
    return action_taken

# def handle_signal_targetcoin(symbol, args, manager, signal, open_position_data, symbols_allowed, symbols_allowed_long, symbols_allowed_short, is_open_position, long_mode, short_mode, graceful_stop_long, graceful_stop_short):
#     global unique_active_symbols, active_long_symbols, active_short_symbols

#     # Log receipt of the signal and handle neutral signals early
#     if signal == "neutral":
#         logging.info(f"Received neutral signal for symbol {symbol}. Checking open positions.")
#         action_taken = start_thread_for_open_symbol(symbol, args, manager, signal, 
#                                                     has_open_long=symbol in active_long_symbols, 
#                                                     has_open_short=symbol in active_short_symbols, 
#                                                     long_mode=long_mode, short_mode=short_mode, 
#                                                     graceful_stop_long=graceful_stop_long, 
#                                                     graceful_stop_short=graceful_stop_short)
#         return action_taken

#     # Gather open position symbols and log the current state
#     open_position_symbols = {standardize_symbol(pos['symbol']) for pos in open_position_data}
#     logging.info(f"Open position symbols: {open_position_symbols}")

#     # Determine the type of signal (long/short)
#     signal_long = signal.lower() == "long"
#     signal_short = signal.lower() == "short"

#     # Log the status of the bot's current positions
#     current_long_positions = len(active_long_symbols)
#     current_short_positions = len(active_short_symbols)
#     logging.info(f"Handling signal for {'open position' if is_open_position else 'new rotator'} symbol {symbol}. "
#                  f"Current long positions: {current_long_positions}. "
#                  f"Current short positions: {current_short_positions}. "
#                  f"Unique active symbols: {len(unique_active_symbols)}")

#     logging.info(f"Active long symbols: {active_long_symbols}")
#     logging.info(f"Active short symbols: {active_short_symbols}")

#     # Check if there are open long/short positions for the symbol
#     has_open_long = symbol in active_long_symbols
#     has_open_short = symbol in active_short_symbols

#     # Log details about the current state and modes
#     logging.info(f"{'Open position' if is_open_position else 'New rotator'} symbol {symbol} - "
#                  f"Has open long: {has_open_long}, Has open short: {has_open_short}")
#     logging.info(f"Signal: {signal}, Long Mode: {long_mode}, Short Mode: {short_mode}")

#     # Flags to track if actions are taken
#     action_taken_long = False
#     action_taken_short = False

#     # Determine if the bot can add a new long/short symbol
#     can_add_new_long_symbol = current_long_positions < symbols_allowed
#     can_add_new_short_symbol = current_short_positions < symbols_allowed

#     # Handle long signals
#     if signal_long and long_mode:
#         if (can_add_new_long_symbol or symbol in unique_active_symbols) and not has_open_long:
#             if graceful_stop_long and not is_open_position:
#                 logging.info(f"Skipping long signal for {symbol} due to graceful stop long enabled and no open long position.")
#             elif not (symbol in long_threads and long_threads[symbol][0].is_alive()):
#                 logging.info(f"Starting long thread for symbol {symbol}.")
#                 action_taken_long = start_thread_for_symbol(symbol, args, manager, signal, "long", has_open_long, has_open_short)
#             else:
#                 logging.info(f"Long thread already running for symbol {symbol}. Skipping.")
#         else:
#             logging.info(f"Cannot open long position for {symbol}. Long positions limit reached or position already exists.")

#     # Handle short signals
#     if signal_short and short_mode:
#         if (can_add_new_short_symbol or symbol in unique_active_symbols) and not has_open_short:
#             if graceful_stop_short and not is_open_position:
#                 logging.info(f"Skipping short signal for {symbol} due to graceful stop short enabled and no open short position.")
#             elif not (symbol in short_threads and short_threads[symbol][0].is_alive()):
#                 logging.info(f"Starting short thread for symbol {symbol}.")
#                 action_taken_short = start_thread_for_symbol(symbol, args, manager, signal, "short", has_open_long, has_open_short)
#             else:
#                 logging.info(f"Short thread already running for symbol {symbol}. Skipping.")
#         else:
#             logging.info(f"Cannot open short position for {symbol}. Short positions limit reached or position already exists.")

#     # Update active symbols based on actions taken
#     if action_taken_long or action_taken_short:
#         unique_active_symbols.add(symbol)
#         if action_taken_long:
#             active_long_symbols.add(symbol)
#         if action_taken_short:
#             active_short_symbols.add(symbol)
#         logging.info(f"Action taken for {'open position' if is_open_position else 'new rotator'} symbol {symbol}.")
#     else:
#         logging.info(f"No action taken for {'open position' if is_open_position else 'new rotator'} symbol {symbol}.")

#     # Return the result indicating whether any action was taken
#     return action_taken_long or action_taken_short

def handle_signal(symbol, args, manager, signal, open_position_data, symbols_allowed, symbols_allowed_long, symbols_allowed_short, is_open_position, long_mode, short_mode, graceful_stop_long, graceful_stop_short):
    """
    Handle trading signals for a given symbol and manage open positions or start new trades.

    Parameters:
    symbol (str): The trading symbol for which the signal is received.
    args (dict): Additional arguments required for handling the signal.
    manager (object): The manager object responsible for handling trades.
    signal (str): The type of signal received ('long', 'short', or 'neutral').
    open_position_data (list): List of dictionaries containing data about open positions.
    symbols_allowed (set): Set of symbols that are allowed for trading.
    is_open_position (bool): Flag indicating if the signal is for an open position.
    long_mode (bool): Flag indicating if long trades are allowed.
    short_mode (bool): Flag indicating if short trades are allowed.
    graceful_stop_long (bool): Flag indicating if long trades should be gracefully stopped.
    graceful_stop_short (bool): Flag indicating if short trades should be gracefully stopped.

    Returns:
    bool: True if any action was taken (starting a new thread for a trade), False otherwise.
    """
    global unique_active_symbols, active_long_symbols, active_short_symbols

    # Log receipt of the signal and handle neutral signals for open positions early
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Received signal '{signal}' for symbol {symbol}. Checking open positions and starting threads if needed.")

    # Gather open position symbols and log the current state
    open_position_symbols = {standardize_symbol(pos['symbol']) for pos in open_position_data}
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Open position symbols: {open_position_symbols}")

    # Determine the type of signal (long/short/neutral)
    signal_long = signal.lower() == "long"
    signal_short = signal.lower() == "short"
    signal_neutral = signal.lower() == "neutral"

    # Log the status of the bot's current positions
    current_long_positions = len(active_long_symbols)
    current_short_positions = len(active_short_symbols)
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Handling signal for {'open position' if is_open_position else 'new rotator'} symbol {symbol}. "
                 f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Current long positions: {current_long_positions}. "
                 f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Current short positions: {current_short_positions}. "
                 f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Unique active symbols: {len(unique_active_symbols)}")

    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Active long symbols: {active_long_symbols}")
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Active short symbols: {active_short_symbols}")

    # Check if there are open long/short positions for the symbol
    has_open_long = symbol in active_long_symbols
    has_open_short = symbol in active_short_symbols

    # Log details about the current state and modes
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] {'Open position' if is_open_position else 'New rotator'} symbol {symbol} - "
                 f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Has open long: {has_open_long}, Has open short: {has_open_short}")
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Signal: {signal}, Long Mode: {long_mode}, Short Mode: {short_mode}")

    # Initialize action_taken variables to avoid reference errors
    action_taken_long = False
    action_taken_short = False

    # Handle neutral signals for open positions (optional logic to trigger action on neutral signals)
    if signal_neutral and is_open_position:
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Neutral signal received for symbol {symbol}. Managing open position.")
        action_taken = start_thread_for_open_symbol(symbol, args, manager, signal, 
                                                    has_open_long=has_open_long, 
                                                    has_open_short=has_open_short, 
                                                    long_mode=long_mode, 
                                                    short_mode=short_mode, 
                                                    graceful_stop_long=graceful_stop_long, 
                                                    graceful_stop_short=graceful_stop_short,
                                                    symbols_allowed=symbols_allowed,
                                                    symbols_allowed_long=symbols_allowed_long,
                                                    symbols_allowed_short=symbols_allowed_short)
        return action_taken

    # Handle long signals for open positions or new symbols
    if signal_long and long_mode and not has_open_long:
        if graceful_stop_long:
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Skipping long signal for {symbol} due to graceful stop long enabled.")
        else:
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Starting long thread for symbol {symbol}.")
            action_taken_long = start_thread_for_symbol(symbol, args, manager, signal, "long", has_open_long, has_open_short, symbols_allowed, symbols_allowed_long, symbols_allowed_short)
            if action_taken_long:
                active_long_symbols.add(symbol)
                unique_active_symbols.add(symbol)

    # Handle short signals for open positions or new symbols
    if signal_short and short_mode and not has_open_short:
        if graceful_stop_short:
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Skipping short signal for {symbol} due to graceful stop short enabled.")
        else:
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Starting short thread for symbol {symbol}.")
            action_taken_short = start_thread_for_symbol(symbol, args, manager, signal, "short", has_open_long, has_open_short, symbols_allowed, symbols_allowed_long, symbols_allowed_short)
            if action_taken_short:
                active_short_symbols.add(symbol)
                unique_active_symbols.add(symbol)

    # If no action was taken for long or short, log it
    if not action_taken_long and not action_taken_short:
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] No action taken for {'open position' if is_open_position else 'new rotator'} symbol {symbol}.")

    # Return the result indicating whether any action was taken
    return action_taken_long or action_taken_short




def update_active_symbols(open_position_symbols):
    """
    COMMENT: This function forcibly synchronizes local sets with
    what the exchange says is actually open (open_position_symbols).
    It's typically called periodically in the rotation loop.
    """
    global active_symbols, active_long_symbols, active_short_symbols, unique_active_symbols
    active_symbols = open_position_symbols
    active_long_symbols = {symbol for symbol in open_position_symbols if is_long_position(symbol)}
    active_short_symbols = {symbol for symbol in open_position_symbols if is_short_position(symbol)}
    unique_active_symbols = active_long_symbols.union(active_short_symbols)
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated active symbols ({len(active_symbols)}): {active_symbols}")
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated active long symbols ({len(active_long_symbols)}): {active_long_symbols}")
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated active short symbols ({len(active_short_symbols)}): {active_short_symbols}")
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Updated unique active symbols ({len(unique_active_symbols)}): {unique_active_symbols}")

# def manage_excess_threads(symbols_allowed, symbols_allowed_long, symbols_allowed_short):
#     global active_symbols, active_long_symbols, active_short_symbols
#     long_positions = {symbol for symbol in active_symbols if symbol in active_long_symbols}
#     short_positions = {symbol for symbol in active_symbols if symbol in active_short_symbols}

#     logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Managing excess threads. Total long positions: {len(long_positions)}, Total short positions: {len(short_positions)}")

#     excess_long_count = len(long_positions) - symbols_allowed
#     excess_short_count = len(short_positions) - symbols_allowed

#     while excess_long_count > 0:
#         symbol_to_remove = long_positions.pop()
#         remove_thread_for_symbol(symbol_to_remove)
#         logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Removed excess long thread for symbol: {symbol_to_remove}")
#         excess_long_count -= 1

#     while excess_short_count > 0:
#         symbol_to_remove = short_positions.pop()
#         remove_thread_for_symbol(symbol_to_remove)
#         logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Removed excess short thread for symbol: {symbol_to_remove}")
#         excess_short_count -= 1

def is_long_position(symbol):
    pos_data = getattr(manager.exchange, f"get_all_open_positions_{args.exchange.lower()}")()
    is_long = any(standardize_symbol(pos['symbol']) == symbol and pos['side'].lower() == 'long' for pos in pos_data)
    logging.debug(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Checked if {symbol} is a long position: {is_long}")
    return is_long

def is_short_position(symbol):
    pos_data = getattr(manager.exchange, f"get_all_open_positions_{args.exchange.lower()}")()
    is_short = any(standardize_symbol(pos['symbol']) == symbol and pos['side'].lower() == 'short' for pos in pos_data)
    logging.debug(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Checked if {symbol} is a short position: {is_short}")
    return is_short

def remove_thread_for_symbol(symbol):
    global unique_active_symbols
    if symbol in long_threads:
        thread, thread_completed = long_threads[symbol]
    elif symbol in short_threads:
        thread, thread_completed = short_threads[symbol]
    else:
        return

    if thread:
        thread_completed.set()
        thread.join()
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Removed thread for symbol {symbol}.")

    if symbol in long_threads:
        del long_threads[symbol]
    if symbol in short_threads:
        del short_threads[symbol]
    
    active_long_symbols.discard(symbol)
    active_short_symbols.discard(symbol)
    active_symbols.discard(symbol)
    unique_active_symbols.discard(symbol)


def start_thread_for_open_symbol(symbol, args, manager, mfirsi_signal, has_open_long, has_open_short, long_mode, short_mode, graceful_stop_long, graceful_stop_short, symbols_allowed, symbols_allowed_long, symbols_allowed_short):
    global unique_active_symbols, long_threads, short_threads, active_long_symbols, active_short_symbols, active_symbols
    action_taken = False

    # Log if there is an alive thread for the long side
    if symbol in long_threads and long_threads[symbol][0].is_alive():
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] A long thread is currently alive for symbol {symbol}.")
    else:
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] No active long thread alive for symbol {symbol}.")

    # Log if there is an alive thread for the short side
    if symbol in short_threads and short_threads[symbol][0].is_alive():
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] A short thread is currently alive for symbol {symbol}.")
    else:
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] No active short thread alive for symbol {symbol}.")

    # Handle neutral signals by managing open positions
    if mfirsi_signal == "neutral":
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Neutral signal received for {symbol}. Managing open positions.")

        if has_open_long and not (symbol in long_threads and long_threads[symbol][0].is_alive()):
            thread_started = start_thread_for_symbol(symbol, args, manager, mfirsi_signal, "long", has_open_long, has_open_short, symbols_allowed, symbols_allowed_long, symbols_allowed_short)
            action_taken = action_taken or thread_started
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] [DEBUG] {'Started' if thread_started else 'Failed to start'} long thread for symbol {symbol} based on neutral signal")

        if has_open_short and not (symbol in short_threads and short_threads[symbol][0].is_alive()):
            thread_started = start_thread_for_symbol(symbol, args, manager, mfirsi_signal, "short", has_open_long, has_open_short, symbols_allowed, symbols_allowed_long, symbols_allowed_short)
            action_taken = action_taken or thread_started
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] [DEBUG] {'Started' if thread_started else 'Failed to start'} short thread for symbol {symbol} based on neutral signal")

    else:
        # Start long thread if long mode is enabled, there is an open long position, and graceful stop is not active
        if long_mode and has_open_long and not graceful_stop_long and not (symbol in long_threads and long_threads[symbol][0].is_alive()):
            thread_started = start_thread_for_symbol(symbol, args, manager, mfirsi_signal, "long", has_open_long, has_open_short, symbols_allowed, symbols_allowed_long, symbols_allowed_short)
            action_taken = action_taken or thread_started
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] [DEBUG] {'Started' if thread_started else 'Failed to start'} long thread for open symbol {symbol}")

        # Start short thread if short mode is enabled, there is an open short position, and graceful stop is not active
        if short_mode and has_open_short and not graceful_stop_short and not (symbol in short_threads and short_threads[symbol][0].is_alive()):
            thread_started = start_thread_for_symbol(symbol, args, manager, mfirsi_signal, "short", has_open_long, has_open_short, symbols_allowed, symbols_allowed_long, symbols_allowed_short)
            action_taken = action_taken or thread_started
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] [DEBUG] {'Started' if thread_started else 'Failed to start'} short thread for open symbol {symbol}")

    # Log if no action was taken
    if not action_taken:
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] No thread started for open symbol {symbol}.")
    
    return action_taken

def start_thread_for_symbol(
    symbol, args, manager, mfirsi_signal, action, 
    has_open_long, has_open_short,
    symbols_allowed, symbols_allowed_long, symbols_allowed_short
):
    """
    COMMENT: This is a key function that actually spawns the 'run_bot' thread
    for a given symbol, passing the relevant parameters. It also updates the
    dictionaries that track which threads are running for which symbol.
    """
    global unique_active_symbols, long_threads, short_threads
    global active_long_symbols, active_short_symbols, active_symbols

    # 1) We can read or pass symbols_allowed_long / symbols_allowed_short into this function.
    #    If you have them in a global or you pass them in from the caller, that’s up to you.
    #    Let’s assume we pass them in from the caller for clarity:
    #       def start_thread_for_symbol(symbol, args, manager, mfirsi_signal, action,
    #                                   has_open_long, has_open_short,
    #                                   symbols_allowed, symbols_allowed_long, symbols_allowed_short):

    # Already in your code: do not exceed total symbol limit
    if len(unique_active_symbols) >= symbols_allowed and symbol not in unique_active_symbols:
        logging.info(f"[[{symbol}]] Cannot start new thread. Reached max total allowed symbols ({symbols_allowed}).")
        return False

    # 2) SIDE-BASED CAPACITY LOGIC:
    #    We'll check if we are about to open a new long or short that is NOT already open.
    #    If it’s already open (has_open_long or has_open_short is True), we let it pass
    #    because we’re just “managing” an already-open position.

    # Count how many are currently open in each side:
    current_long_count = len(active_long_symbols)
    current_short_count = len(active_short_symbols)

    # If action == "long" and we *don't* already have an open long for this symbol:
    if action == "long" and not has_open_long:
        if current_long_count >= symbols_allowed_long:
            logging.info(f"[[{symbol}]] Skipping new LONG thread. Already reached max long positions ({symbols_allowed_long}).")
            return False
        # Additionally, if there's an existing long thread running:
        if symbol in long_threads and long_threads[symbol][0].is_alive():
            logging.info(f"[[{symbol}]] Long thread already running for this symbol. Skipping.")
            return False

    # Similarly for short:
    if action == "short" and not has_open_short:
        if current_short_count >= symbols_allowed_short:
            logging.info(f"[[{symbol}]] Skipping new SHORT thread. Already reached max short positions ({symbols_allowed_short}).")
            return False
        # Additionally, if there's an existing short thread running:
        if symbol in short_threads and short_threads[symbol][0].is_alive():
            logging.info(f"[[{symbol}]] Short thread already running for this symbol. Skipping.")
            return False

    elif action == "neutral":
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Handling neutral signal for {symbol}, managing open positions.")
        if not (symbol in long_threads and long_threads[symbol][0].is_alive()) and has_open_long:
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Starting long thread for symbol {symbol} based on neutral signal.")
            action = "long"
        elif not (symbol in short_threads and short_threads[symbol][0].is_alive()) and has_open_short:
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] Starting short thread for symbol {symbol} based on neutral signal.")
            action = "short"
        else:
            logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) [[{symbol}]] No thread started for symbol {symbol} with neutral signal.")
            return False

    thread_completed = threading.Event()
    thread = threading.Thread(
        target=run_bot,
        args=(
            symbol, args, market_maker, manager, args.account_name,
            symbols_allowed, latest_rotator_symbols, thread_completed,
            mfirsi_signal, action
        )
    )

    if action == "long":
        long_threads[symbol] = (thread, thread_completed)
        active_long_symbols.add(symbol)

    elif action == "short":
        short_threads[symbol] = (thread, thread_completed)
        active_short_symbols.add(symbol)

    active_symbols.add(symbol)
    unique_active_symbols.add(symbol)
    thread.start()
    logging.info(f"[[{symbol}]] Started thread for symbol {symbol} with action {action}.")
    return True

def fetch_updated_symbols(args, manager, whitelist=None):
    current_time = time.time()
    
    # Check if the cached data is still valid
    if current_time - rotator_symbols_cache['timestamp'] < CACHE_DURATION:
        logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Using cached rotator symbols")
        return rotator_symbols_cache['symbols']
    
    # Fetch new data if cache is expired
    strategy = args.strategy.lower()
    potential_symbols = []

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
    
    # Log only the first 5 symbols for brevity
    symbols_to_log = list(rotator_symbols_cache['symbols'])[:5]
    logging.info(f"(caller: {inspect.stack()[1].function}, func: {inspect.currentframe().f_code.co_name}, line: {inspect.currentframe().f_lineno}) Fetched new rotator symbols: {symbols_to_log}...")
    return rotator_symbols_cache['symbols']



def log_symbol_details(strategy, symbols):
    logging.info(f"Potential symbols for {strategy}: {symbols}")


# def lbank_auto_rotation(args, market_maker, manager, symbols_allowed):
#     open_position_symbols = {standardize_symbol(pos['symbol']) for pos in market_maker.exchange.get_all_open_positions_binance()}
#     logging.info(f"Open position symbols: {open_position_symbols}")

init(autoreset=True)

if __name__ == '__main__':
    sword = f"{Fore.CYAN}====={Fore.WHITE}||{Fore.RED}====>"

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

    manager = Manager(
        market_maker.exchange,
        exchange_name=args.exchange,
        data_source_exchange=config.api.data_source_exchange,
        api=config.api.mode,
        path=Path("data", config.api.filename),
        url=f"{config.api.url}{config.api.filename}"
    )

    print(f"Using exchange {config.api.data_source_exchange} for API data")

    whitelist = config.bot.whitelist
    blacklist = config.bot.blacklist
    max_usd_value = config.bot.max_usd_value

    for exch in config.exchanges:
        if exch.name == exchange_name and exch.account_name == args.account_name:
            symbols_allowed = getattr(exch, 'symbols_allowed', 10)
            symbols_allowed_long = getattr(exch, 'symbols_allowed_long', symbols_allowed)
            symbols_allowed_short = getattr(exch, 'symbols_allowed_short', symbols_allowed)
            
            logging.info(f"symbols_allowed={symbols_allowed}, symbols_allowed_long={symbols_allowed_long}, symbols_allowed_short={symbols_allowed_short}")
            break
    else:
        logging.info(f"No matching exchange found. Defaulting symbols_allowed to 10.")
        symbols_allowed = 10
        symbols_allowed_long = 5
        symbols_allowed_short = 2

    table_manager = LiveTableManager()
    display_thread = threading.Thread(target=table_manager.display_table)
    display_thread.daemon = True
    display_thread.start()

    # Removed redundant calls and initialization
    while True:
        try:
            whitelist = config.bot.whitelist
            blacklist = config.bot.blacklist
            max_usd_value = config.bot.max_usd_value

            match exchange_name.lower():
                case 'bybit':
                    bybit_auto_rotation(args, market_maker, manager, symbols_allowed, symbols_allowed_long, symbols_allowed_short)
                case _:
                    logging.warning(f"Auto-rotation not implemented for exchange: {exchange_name}")

            logging.info(f"Active symbols: {active_symbols}")
            logging.info(f"Total active symbols: {len(active_symbols)}")

            time.sleep(10)
        except Exception as e:
            logging.info(f"Exception caught in main loop: {e}")
            logging.info(traceback.format_exc())
