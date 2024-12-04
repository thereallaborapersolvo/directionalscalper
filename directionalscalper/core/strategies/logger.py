# logger.py

import os
import logging
import logging.handlers as handlers  # For RotatingFileHandler
from pathlib import Path
import re

def is_dumb_terminal():
    _term = os.environ.get("TERM", "")
    is_dumb = _term.lower() in ("", "dumb", "unknown")
    return is_dumb

class SymbolFileHandler(logging.Handler):
    """
    Custom logging handler that routes logs to symbol-specific files based on the log message.
    Assumes that the log message contains the symbol in square brackets, e.g., "Current price for [BTCUSD]: 30000"
    """
    def __init__(self, base_log_dir='logs', base_filename='BybitBaseStrategy.log', **kwargs):
        super().__init__()
        self.base_log_dir = Path(base_log_dir)
        self.base_log_dir.mkdir(exist_ok=True, parents=True)
        self.base_filename = base_filename
        self.symbol_handlers = {}  # Cache for symbol-specific handlers

        # General handler for logs without a symbol
        self.general_handler = handlers.RotatingFileHandler(
            self.base_log_dir / self.base_filename,
            maxBytes=5_000_000,  # 5 MB
            backupCount=5
        )
        formatter = logging.Formatter(
            fmt="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
            datefmt="%Y-%m-%d %H:%M:%S",
        )
        self.general_handler.setFormatter(formatter)
        self.general_handler.setLevel(logging.INFO)
        self.symbol_handlers['general'] = self.general_handler

    def emit(self, record):
        try:
            message = record.getMessage()
            # Debugging Statement: Uncomment for debugging
            # print(f"SymbolFileHandler emit called with message: {message}")
            
            # Regex to extract the symbol from messages like "Current price for [BTCUSD]: ..."
            match = re.search(r'\[\[(.*?)\]\]', message)
            if match:
                symbol = match.group(1)
                handler = self.symbol_handlers.get(symbol)
                if not handler:
                    # Create a new handler for the symbol
                    symbol_filename = f"BybitBaseStrategy_{symbol}.log"
                    handler = handlers.RotatingFileHandler(
                        self.base_log_dir / symbol_filename,
                        maxBytes=5_000_000,  # 5 MB
                        backupCount=5
                    )
                    formatter = logging.Formatter(
                        fmt="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
                        datefmt="%Y-%m-%d %H:%M:%S",
                    )
                    handler.setFormatter(formatter)
                    handler.setLevel(logging.DEBUG)
                    self.symbol_handlers[symbol] = handler
                    # Debugging Statement: Uncomment for debugging
                    # print(f"Created new handler for symbol: {symbol}")
                # Use the symbol-specific handler
                handler.emit(record)
                # Debugging Statement: Uncomment for debugging
                # print(f"Logged message to {symbol}_BybitBaseStrategy.log")
            else:
                # Use the general handler
                self.symbol_handlers['general'].emit(record)
                # Debugging Statement: Uncomment for debugging
                # print(f"Logged message to {self.base_filename}")
        except Exception as e:
            # Print exception details for debugging
            print(f"Error in SymbolFileHandler emit: {e}")
            self.handleError(record)

def Logger(
    logger_name: str,
    filename: str,
    level: str = "info",
    console_level: str = "error",  # Changed default value to "error"
    backups: int = 5,
    bytes: int = 5000000,
    stream: bool = False,
):
    """
    Initializes and returns a logger with a custom SymbolFileHandler.
    """
    log = logging.getLogger(logger_name)
    if log.handlers:
        # Logger is already configured, do not add new handlers
        return log

    # Initialize the custom SymbolFileHandler
    symbol_handler = SymbolFileHandler(base_log_dir='logs', base_filename=filename)
    log.addHandler(symbol_handler)

    # Optionally add a stream handler for console output
    if stream or not is_dumb_terminal():
        consoleHandler = logging.StreamHandler()  # Use logging.StreamHandler instead of handlers.StreamHandler
        formatter = logging.Formatter(
            fmt="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
            datefmt="%Y-%m-%d %H:%M:%S",
        )
        consoleHandler.setFormatter(formatter)
        console_level = logging.getLevelName(console_level.upper())
        consoleHandler.setLevel(console_level)  # Set the level for console output
        log.addHandler(consoleHandler)

    # Set the overall log level
    level = logging.getLevelName(level.upper())
    log.setLevel(level)

    # Prevent log messages from propagating to the root logger
    log.propagate = False

    return log
