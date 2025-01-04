import time
import json
import os
import copy
import pytz
import threading
import traceback
from threading import Thread, Lock
from datetime import datetime, timedelta

from directionalscalper.core.strategies.bybit.bybit_strategy import BybitStrategy
from directionalscalper.core.exchanges.bybit import BybitExchange
from directionalscalper.core.strategies.logger import Logger
from live_table_manager import shared_symbols_data

# logger = Logger(logger_name="BybitSpotGridStrategy", filename="BybitSpotGridStrategy.log", stream=True)
logger = Logger(logger_name="BybitSpotGridStrategy", filename="BybitSpotGridStrategy.log", stream=True)

symbol_locks = {}

class BybitSpotGridStrategy(BybitStrategy):
    def __init__(self, exchange, manager, config, symbols_allowed=None, rotator_symbols_standardized=None, mfirsi_signal=None):
        super().__init__(exchange, config, manager, symbols_allowed)
        self.mfirsi_signal = mfirsi_signal
        self.is_order_history_populated = False
        self.last_health_check_time = time.time()
        self.health_check_interval = 600
        self.running = False  # Single flag for running
        try:
            self.wallet_exposure_limit = self.config.wallet_exposure_limit
            self.levels = self.config.linear_grid['levels']
            self.strength = self.config.linear_grid['strength']
            self.outer_price_distance = self.config.linear_grid['outer_price_distance']
            self.reissue_threshold = self.config.linear_grid['reissue_threshold']
            self.buffer_percentage = self.config.linear_grid['buffer_percentage']
            self.enforce_full_grid = self.config.linear_grid['enforce_full_grid']
            self.initial_entry_buffer_pct = self.config.linear_grid['initial_entry_buffer_pct']
            self.min_buffer_percentage = self.config.linear_grid['min_buffer_percentage']
            self.max_buffer_percentage = self.config.linear_grid['max_buffer_percentage']
            self.min_outer_price_distance = self.config.linear_grid['min_outer_price_distance']
            self.max_outer_price_distance = self.config.linear_grid['max_outer_price_distance']
            self.upnl_threshold_pct = self.config.upnl_threshold_pct
            self.volume_check = self.config.volume_check
            self.max_usd_value = self.config.max_usd_value
            self.blacklist = self.config.blacklist
            self.upnl_profit_pct = self.config.upnl_profit_pct
            self.max_upnl_profit_pct = self.config.max_upnl_profit_pct
            self.stoploss_enabled = self.config.stoploss_enabled
            self.stoploss_upnl_pct = self.config.stoploss_upnl_pct
            self.entry_during_autoreduce = self.config.entry_during_autoreduce
            self.max_qty_percent = self.config.linear_grid['max_qty_percent']
        except AttributeError as e:
            logger.error(f"Failed to initialize attributes from config: {e}")

    def run(self, symbol, rotator_symbols_standardized=None, mfirsi_signal=None):
        try:
            standardized_symbol = symbol.upper()  # Standardize the symbol name
            logger.info(f"Standardized symbol: {standardized_symbol}")
            current_thread_id = threading.get_ident()

            if standardized_symbol not in symbol_locks:
                symbol_locks[standardized_symbol] = threading.Lock()

            if symbol_locks[standardized_symbol].acquire(blocking=False):
                logger.info(f"Lock acquired for symbol {standardized_symbol} by thread {current_thread_id}")
                try:
                    self.running = True
                    self.run_trades(standardized_symbol, rotator_symbols_standardized, mfirsi_signal)
                finally:
                    symbol_locks[standardized_symbol].release()
                    logger.info(f"Lock released for symbol {standardized_symbol} by thread {current_thread_id}")
            else:
                logger.info(f"Failed to acquire lock for symbol: {standardized_symbol}")
        except Exception as e:
            logger.info(f"Exception in run function {e}")

    def run_trades(self, symbol, rotator_symbols_standardized=None, mfirsi_signal=None):
        try:
            logger.info(f"Starting to process symbol: {symbol}")
            logger.info(f"Initializing default values for symbol: {symbol}")

            previous_pos_qty = 0

            min_qty = None
            current_price = None
            total_equity = None
            available_equity = None
            one_minute_volume = None
            five_minute_volume = None
            one_minute_distance = None
            five_minute_distance = None
            ma_trend = 'neutral'  # Initialize with default value
            ema_trend = 'undefined'  # Initialize with default value
            pos_qty = 0
            upnl = 0
            cum_realised_pnl = 0
            pos_price = None

            last_equity_fetch_time = 0
            equity_refresh_interval = 30  # 30 minutes in seconds

            self.setup_exchange(symbol)

            quote_currency = "USDT"
            max_retries = 5
            retry_delay = 5

            while self.running:
                current_time = time.time()
                iteration_start_time = time.time()

                logger.info(f"Trading {symbol} in while loop")

                if not self.running:
                    logger.info(f"Killing thread for {symbol}")
                    break

                current_time = time.time()

                iteration_start_time = time.time()

                total_equity = self.retry_api_call(self.exchange.get_balance_bybit, quote_currency)
                available_equity = self.retry_api_call(self.exchange.get_available_balance_bybit, quote_currency)
                last_equity_fetch_time = current_time

                logger.info(f"Total equity: {total_equity}")
                logger.info(f"Available equity: {available_equity}")
                    
                if total_equity is None:
                    logger.warning("Failed to fetch total_equity. Skipping this iteration.")
                    time.sleep(10)  # wait for a short period before retrying
                    continue

                blacklist = self.config.blacklist
                if symbol in blacklist:
                    logger.info(f"Symbol {symbol} is in the blacklist. Stopping operations for this symbol.")
                    break

                current_price = self.exchange.get_current_price(symbol)
                order_book = self.exchange.get_orderbook(symbol)

                if 'asks' in order_book and len(order_book['asks']) > 0:
                    best_ask_price = order_book['asks'][0][0]
                    self.last_known_ask[symbol] = best_ask_price  # Update last known ask price
                else:
                    best_ask_price = self.last_known_ask.get(symbol)  # Use last known ask price

                if 'bids' in order_book and len(order_book['bids']) > 0:
                    best_bid_price = order_book['bids'][0][0]
                    self.last_known_bid[symbol] = best_bid_price  # Update last known bid price
                else:
                    best_bid_price = self.last_known_bid.get(symbol)  # Use last known bid price

                moving_averages = self.get_all_moving_averages(symbol)

                open_symbols = self.retry_api_call(self.exchange.get_open_symbols_bybit)

                market_data = self.get_market_data_with_retry(symbol, max_retries=100, retry_delay=5)
                min_qty = float(market_data["min_qty"])

                position_details = self.retry_api_call(self.exchange.get_positions_bybit, symbol)
                pos_qty = position_details.get('qty', 0)

                logger.info(f"Previous pos qty for {symbol}: {previous_pos_qty}")
                logger.info(f"Current pos qty for {symbol}: {pos_qty}")

                previous_pos_qty = pos_qty

                if not self.running:
                    shared_symbols_data.pop(symbol, None)
                    self.cancel_grid_orders(symbol, "buy")
                    self.active_grids.discard(symbol)
                    self.cleanup_before_termination(symbol)
                    logger.info("Operations have terminated. Exiting the loop.")
                    break

                trading_allowed = self.can_trade_new_symbol(open_symbols, self.symbols_allowed, symbol)
                logger.info(f"Checking trading for symbol {symbol}. Can trade: {trading_allowed}")
                logger.info(f"Symbol: {symbol}, In open_symbols: {symbol in open_symbols}, Trading allowed: {trading_allowed}")

                one_minute_volume, five_minute_volume, one_minute_distance, five_minute_distance, ma_trend, ema_trend, funding_rate, hma_trend, eri_trend = self.extract_metrics(symbol)

                self.adjust_risk_parameters()

                long_dynamic_amount = self.calculate_dynamic_amounts_notional(
                    symbol=symbol,
                    total_equity=total_equity,
                    best_ask_price=best_ask_price,
                    best_bid_price=best_bid_price
                )

                logger.info(f"Long dynamic amount: {long_dynamic_amount} for {symbol}")

                cum_realised_pnl = position_details.get("cum_realised", 0)
                pos_price = position_details.get('avg_price', None)

                take_profit = self.calculate_quickscalp_take_profit_dynamic_distance(pos_price, symbol, min_upnl_profit_pct=upnl_profit_pct, max_upnl_profit_pct=max_upnl_profit_pct)

                short_stop_loss = None
                long_stop_loss = None

                initial_short_stop_loss = None
                initial_long_stop_loss = None

                self.auto_reduce_logic_grid_hardened(
                    symbol,
                    min_qty,
                    pos_price,
                    pos_qty,
                    upnl,
                    auto_reduce_enabled,
                    total_equity,
                    current_price,
                    long_dynamic_amount,
                    auto_reduce_start_pct,
                    min_buffer_percentage_ar,
                    max_buffer_percentage_ar,
                    upnl_auto_reduce_threshold,
                    self.current_leverage
                )

                self.auto_reduce_percentile_logic(
                    symbol,
                    pos_qty,
                    pos_price,
                    percentile_auto_reduce_enabled,
                    auto_reduce_start_pct,
                    auto_reduce_maxloss_pct,
                    long_dynamic_amount
                )

                self.liq_stop_loss_logic(
                    pos_qty,
                    pos_price,
                    pos_liquidation_price,
                    liq_stoploss_enabled,
                    symbol,
                    liq_price_stop_pct
                )

                self.stop_loss_logic(
                    pos_qty,
                    pos_price,
                    stoploss_enabled,
                    symbol,
                    stoploss_upnl_pct
                )

                self.cancel_auto_reduce_orders_bybit(
                    symbol,
                    total_equity,
                    max_pos_balance_pct,
                    open_position_data,
                    pos_qty
                )

                take_profit = self.calculate_quickscalp_take_profit_dynamic_distance(pos_price, symbol, min_upnl_profit_pct=upnl_profit_pct, max_upnl_profit_pct=max_upnl_profit_pct)

                if pos_qty > 0:
                    new_tp_min, new_tp_max = self.calculate_quickscalp_take_profit_dynamic_distance(
                        pos_price, symbol, upnl_profit_pct, max_upnl_profit_pct
                    )
                    if new_tp_min is not None and new_tp_max is not None:
                        self.next_tp_update = self.update_quickscalp_tp_dynamic(
                            symbol=symbol,
                            pos_qty=pos_qty,
                            upnl_profit_pct=upnl_profit_pct,
                            max_upnl_profit_pct=max_upnl_profit_pct,
                            pos_price=pos_price,
                            last_tp_update=self.next_tp_update,
                            tp_order_counts=tp_order_counts,
                            open_orders=open_orders
                        )

                if self.test_orders_enabled and current_time - self.last_helper_order_cancel_time >= self.helper_interval:
                    if symbol in open_symbols:
                        self.helper_active = True
                        self.helperv2(symbol, long_dynamic_amount)
                    else:
                        logger.info(f"Skipping test orders for {symbol} as it's not in open symbols list.")

                if not self.running:
                    logger.info("Operations have ended. Preparing to exit loop.")
                    shared_symbols_data.pop(symbol, None)

                if previous_pos_qty > 0 and pos_qty == 0:
                    logger.info(f"Position closed for {symbol}. Canceling grid orders.")
                    self.cancel_grid_orders(symbol, "buy")
                    self.cleanup_before_termination(symbol)
                    break

                time.sleep(5)

                symbol_data = {
                    'symbol': symbol,
                    'min_qty': min_qty,
                    'current_price': current_price,
                    'balance': total_equity,
                    'available_bal': available_equity,
                    'volume': five_minute_volume,
                    'spread': five_minute_distance,
                    'ma_trend': ma_trend,
                    'ema_trend': ema_trend,
                    'pos_qty': pos_qty,
                    'upnl': upnl,
                    'cum_pnl': cum_realised_pnl,
                    'pos_price': pos_price
                }

                shared_symbols_data[symbol] = symbol_data

                if self.config.dashboard_enabled:
                    try:
                        dashboard_path = os.path.join(self.config.shared_data_path, "shared_data.json")
                        logger.info(f"Dashboard path: {dashboard_path}")

                        os.makedirs(os.path.dirname(dashboard_path), exist_ok=True)
                        logger.info(f"Directory created: {os.path.dirname(dashboard_path)}")

                        if os.path.exists(dashboard_path):
                            with open(dashboard_path, "r") as file:
                                data = json.load(file)
                                logger.info("Loaded existing data from shared_data.json")
                        else:
                            logger.warning("shared_data.json does not exist. Creating a new file.")
                            data = {}

                        with open(dashboard_path, "w") as file:
                            json.dump(data, file)
                            logger.info("Data saved to shared_data.json")

                    except FileNotFoundError:
                        logger.info(f"File not found: {dashboard_path}")
                    except IOError as e:
                        logger.info(f"I/O error occurred: {e}")
                    except Exception as e:
                        logger.info(f"An unexpected error occurred in saving json: {e}")

                iteration_end_time = time.time()
                iteration_duration = iteration_end_time - iteration_start_time
                logger.info(f"Iteration for symbol {symbol} took {iteration_duration:.2f} seconds")

                time.sleep(3)
        except Exception as e:
            traceback_info = traceback.format_exc()
            logger.info(f"Exception caught in spot strategy '{symbol}': {e}\nTraceback:\n{traceback_info}")
