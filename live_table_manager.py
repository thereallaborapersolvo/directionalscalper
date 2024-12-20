# live_table_manager.py

import threading
import datetime
import time
import logging  # Import the logging module
from rich.console import Console
from rich.live import Live
from rich.table import Table
import copy

# Configure logging
logging.basicConfig(
    level=logging.INFO,  # Capture all levels of log messages
    format='%(asctime)s - %(levelname)s - %(message)s',  # Define log message format
    handlers=[
        logging.FileHandler("/home/labper/directionalscalper_simple2/logs/LiveTableManager.log")  # Log to a file named 'LiveTableManager.log'
    ]
)

# Import shared_symbols_data and BaseStrategy
from directionalscalper.core.strategies.base_strategy import BaseStrategy, shared_symbols_data

class LiveTableManager:
    def __init__(self):
        self.table = self.generate_table()
        self.row_data = {}  # Dictionary to store row data

    def validate_shared_symbols_data(self, shared_data):
        """
        Validates the structure of shared_symbols_data.
        Logs warnings if expected keys are missing.
        """
        for sym, data in shared_data.items():
            if 'symbol' not in data:
                logging.warning(f"Symbol '{sym}' is missing the 'symbol' key in shared_symbols_data.")
            # Add more validations as needed
            required_keys = [
                'min_qty', 'current_price', 'volume', 'spread', 'ema_trend',
                'long_pos_qty', 'short_pos_qty', 'long_upnl', 'short_upnl',
                'long_cum_pnl', 'short_cum_pnl', 'long_pos_price', 'short_pos_price'
            ]
            for key in required_keys:
                if key not in data:
                    logging.warning(f"Symbol '{sym}' is missing the '{key}' key in shared_symbols_data.")

    def generate_table(self) -> Table:
        table = Table(show_header=True, header_style="bold blue", title="DirectionalScalper")
       
        table.add_column("Symbol", style="cyan", min_width=12)
        table.add_column("Min. Qty")
        table.add_column("Price")
        table.add_column("1m Vol")
        table.add_column("5m Spread")
        table.add_column("MA Trend", style="magenta")
        table.add_column("Long Pos. Qty")
        table.add_column("Short Pos. Qty")
        table.add_column("Long uPNL")
        table.add_column("Short uPNL")
        table.add_column("Long cum. PNL")
        table.add_column("Short cum. PnL")
        table.add_column("Long Pos. Price")
        table.add_column("Short Pos. Price")

        current_time = datetime.datetime.now().strftime('%H:%M:%S %d-%m-%Y')
        with BaseStrategy.symbol_management_lock:
            symbols_data_list = list(shared_symbols_data.values())

            if symbols_data_list:
                last_symbol_data = symbols_data_list[-1]
                balance = "{:.4f}".format(float(last_symbol_data.get('balance') or 0))
                available_bal = "{:.4f}".format(float(last_symbol_data.get('available_bal') or 0))
                total_upnl = "{:.4f}".format(sum(
                    float(symbol_data.get('long_upnl', 0) or 0) + float(symbol_data.get('short_upnl', 0) or 0)
                    for symbol_data in symbols_data_list
                ))
                # Styling
                try:
                    upnl_value = float(total_upnl)
                except ValueError:
                    upnl_value = 0.0
                upnl_style = "[italic]" if upnl_value > 9 or upnl_value < -9.5 else "[bold]" if upnl_value > 3.5 or upnl_value < -3.5 else ""
                upnl_color = "[green]" if upnl_value > 1 else "[red]" if upnl_value < -1 else "[grey]"
                styled_upnl = f"{upnl_style}{upnl_color}{total_upnl}[/]"
                table.caption = f"Balance: {balance} | Available: {available_bal} | Total uPnL: {styled_upnl} | Updated: {current_time}"
            else:
                table.caption = f"Loading... {len(shared_symbols_data)} symbols loaded | Updated: {current_time}"

        # Validate shared_symbols_data before rendering
        self.validate_shared_symbols_data(shared_symbols_data)

        # Sorting symbols with type conversion
        sorted_symbols = sorted(
            [symbol_data for symbol_data in symbols_data_list if 'symbol' in symbol_data],
            key=lambda x: (
                -(float(x.get('long_pos_qty', 0) or 0) > 0 or float(x.get('short_pos_qty', 0) or 0) > 0),  # Prioritize positions > 0
                x.get('symbol', '')
            )
        )
        
        for symbol_data in sorted_symbols:
            symbol = symbol_data.get('symbol', '')
            long_pos_qty = float(symbol_data.get('long_pos_qty', 0) or 0)
            short_pos_qty = float(symbol_data.get('short_pos_qty', 0) or 0)
            long_upnl = round(float(symbol_data.get('long_upnl', 0) or 0), 2)
            short_upnl = round(float(symbol_data.get('short_upnl', 0) or 0), 2)
            long_cum_pnl = round(float(symbol_data.get('long_cum_pnl', 0) or 0), 2)
            short_cum_pnl = round(float(symbol_data.get('short_cum_pnl', 0) or 0), 2)
            long_pos_price = round(float(symbol_data.get('long_pos_price', 0) or 0), 8)
            short_pos_price = round(float(symbol_data.get('short_pos_price', 0) or 0), 8)

            # Determine if the entire row should be bold
            is_symbolrowalive = long_pos_qty > 0 or short_pos_qty > 0 

            # Debugging Log for Each Symbol
            logging.debug(f"Symbol: {symbol}, Long uPNL: {long_upnl}, Short uPNL: {short_upnl}, Long Cum PnL: {long_cum_pnl}, Short Cum PnL: {short_cum_pnl}")

            # Helper functions with separate formatting
            def format_numeric_cell(value, is_bold=False, is_highlight=False):
                try:
                    float_value = float(value)
                    formatted_value = f"{float_value:.2f}"
                except (ValueError, TypeError):
                    formatted_value = "0.00"
                
                if is_bold:
                    return f"[b]{formatted_value}[/b]"
                elif is_highlight:
                    return f"[b]{formatted_value}[/b]" if float_value > 0 else formatted_value
                return formatted_value

            def format_text_cell(value, is_bold=False):
                if value is None:
                    return f"[b]N/A[/b]"
                formatted_value = str(value)
                
                if is_bold:
                    return f"[b]{formatted_value}[/b]"
                return formatted_value

            row = [
                format_text_cell(symbol, is_bold=is_symbolrowalive),  # Symbol is textual
                format_numeric_cell(symbol_data.get('min_qty', 0), is_bold=is_symbolrowalive),
                format_numeric_cell(round(float(symbol_data.get('current_price', 0) or 0), 8), is_bold=is_symbolrowalive),
                format_numeric_cell(symbol_data.get('volume', 0), is_bold=is_symbolrowalive),
                format_numeric_cell(symbol_data.get('spread', 0), is_bold=is_symbolrowalive),
                format_text_cell(symbol_data.get('ema_trend', ''), is_bold=is_symbolrowalive),  # MA Trend is textual
                format_numeric_cell(long_pos_qty, is_bold=is_symbolrowalive),
                format_numeric_cell(short_pos_qty, is_bold=is_symbolrowalive),
                format_numeric_cell(long_upnl, is_bold=is_symbolrowalive, is_highlight=True),
                format_numeric_cell(short_upnl, is_bold=is_symbolrowalive, is_highlight=True),
                format_numeric_cell(long_cum_pnl, is_bold=is_symbolrowalive),
                format_numeric_cell(short_cum_pnl, is_bold=is_symbolrowalive),
                format_numeric_cell(long_pos_price, is_bold=is_symbolrowalive),
                format_numeric_cell(short_pos_price, is_bold=is_symbolrowalive)
            ]
            if is_symbolrowalive:
                table.add_row(*row)

        return table

    def display_table(self):
        console = Console()
        with Live(self.table, refresh_per_second=1/3, console=console) as live:
            while True:
                time.sleep(3)
                live.update(self.generate_table())
