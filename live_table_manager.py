import threading
import datetime
import time
from rich.console import Console
from rich.live import Live
from rich.table import Table
import copy

# Import shared_symbols_data and BaseStrategy
from directionalscalper.core.strategies.base_strategy import BaseStrategy, shared_symbols_data

class LiveTableManager:
    def __init__(self):
        self.table = self.generate_table()
        self.row_data = {}  # Dictionary to store row data

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
        table.add_column("Short cum. PNL")
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
                    (symbol_data.get('long_upnl') or 0) + (symbol_data.get('short_upnl') or 0)
                    for symbol_data in symbols_data_list
                ))
            # Styling
            upnl_value = float(total_upnl)
            upnl_style = "[italic]" if upnl_value > 9 or upnl_value < -9.5 else "[bold]" if upnl_value > 3.5 or upnl_value < -3.5 else ""
            upnl_color = "[green]" if upnl_value > 1 else "[red]" if upnl_value < -1 else "[grey]"
            styled_upnl = f"{upnl_style}{upnl_color}{total_upnl}[/]"
            table.caption = f"Balance: {balance} | Available: {available_bal} | Total uPnL: {styled_upnl} | Updated: {current_time}"
        else:
            table.caption = f"Loading... {len(shared_symbols_data)} symbols loaded | Updated: {current_time}"

        # Sorting symbols
        sorted_symbols = sorted(
            [symbol_data for symbol_data in symbols_data_list if 'symbol' in symbol_data],
            key=lambda x: (
                -(x.get('long_pos_qty', 0) > 0 or x.get('short_pos_qty', 0) > 0),  # Prioritize symbols with quantities > 0
                x.get('symbol', '')  # Then sort by symbol name
            )
        )
        
        for symbol_data in sorted_symbols:
            long_pos_qty = symbol_data.get('long_pos_qty', 0)
            short_pos_qty = symbol_data.get('short_pos_qty', 0)
            long_upnl = round(symbol_data.get('long_upnl', 0) or 0, 2)
            short_upnl = round(symbol_data.get('short_upnl', 0) or 0, 2)

            # Determine if the entire row should be bold
            is_symbolrowalive = long_pos_qty > 0 or short_pos_qty > 0 

            # Helper function to format the cell
            def format_cell(value, is_bold=is_symbolrowalive, is_highlight=False):
                if value is None:
                    return f"[b]N/A[/b]"
                if is_bold:
                    return f"[b]{value}[/b]"
                elif is_highlight:
                        return f"[b]{value}[/b]" if value > 0 else str(value)
                return str(value)

            row = [
                    format_cell(symbol_data.get('symbol', '')),
                format_cell(symbol_data.get('min_qty', 0)),
                format_cell(round(symbol_data.get('current_price', 0) or 0, 8)),
                format_cell(symbol_data.get('volume', 0)),
                format_cell(symbol_data.get('spread', 0)),
                format_cell(symbol_data.get('ema_trend', '')),
                format_cell(long_pos_qty),
                format_cell(short_pos_qty),
                format_cell(long_upnl, is_highlight=True),
                format_cell(short_upnl, is_highlight=True),
                format_cell(round(symbol_data.get('long_cum_pnl', 0) or 0, 2)),
                format_cell(round(symbol_data.get('short_cum_pnl', 0) or 0, 2)),
                format_cell(round(symbol_data.get('long_pos_price', 0) or 0, 8)),
                format_cell(round(symbol_data.get('short_pos_price', 0) or 0, 8))
            ]
                if is_symbolrowalive:
                table.add_row(*row)

        return table

    def display_table(self):
        console = Console()
        with Live(self.table, refresh_per_second=1/3) as live:
            while True:
                time.sleep(3)
                    live.update(self.generate_table())
