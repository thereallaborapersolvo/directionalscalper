# /home/labper/directionalscalper_simple3/directionalscalper/core/strategies/logger.py

import os
import logging
import logging.handlers as handlers  # For RotatingFileHandler
from pathlib import Path

def is_dumb_terminal():
    _term = os.environ.get("TERM", "")
    is_dumb = _term.lower() in ("", "dumb", "unknown")
    return is_dumb

class FlushRotatingFileHandler(handlers.RotatingFileHandler):
    """
    Custom RotatingFileHandler that flushes after each emit to ensure logs are written immediately.
    """
    def emit(self, record):
        super().emit(record)
        self.flush()

def Logger(
    logger_name: str,
    filename: str,
    log_dir: str = "logs",  # New parameter for log directory
    level: str = "info",
    console_level: str = "error",
    backups: int = 5,
    bytes: int = 5000000,
    stream: bool = False,
):
    """
    Initializes and returns a logger instance.

    Args:
        logger_name (str): Name of the logger.
        filename (str): Name of the log file.
        log_dir (str, optional): Directory where the log file will be saved. Defaults to "logs".
        level (str, optional): Logging level. Defaults to "info".
        console_level (str, optional): Logging level for the console output. Defaults to "error".
        backups (int, optional): Number of backup files to keep. Defaults to 5.
        bytes (int, optional): Maximum size of a log file in bytes before rotation. Defaults to 5,000,000.
        stream (bool, optional): Whether to enable console output. Defaults to False.

    Returns:
        logging.Logger: Configured logger instance.
    """
    log = logging.getLogger(logger_name)
    if log.handlers:
        # Logger is already configured, do not add new handlers
        return log

    # Formatter to include milliseconds
    formatter = logging.Formatter(
        fmt="%(asctime)s.%(msecs)03d - %(name)s - %(levelname)s - %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )

    # Set up the log directory
    file_path = Path(log_dir)
    file_path.mkdir(parents=True, exist_ok=True)  # Ensure the directory exists
    log_file = file_path / filename

    # Use the custom FlushRotatingFileHandler to ensure immediate writes
    logHandler = FlushRotatingFileHandler(
        log_file, maxBytes=bytes, backupCount=backups
    )
    logHandler.setFormatter(formatter)

    # Set logging level
    level = logging.getLevelName(level.upper())
    log.setLevel(level)
    log.addHandler(logHandler)

    # Optional console handler
    if stream or not is_dumb_terminal():
        consoleHandler = logging.StreamHandler()
        consoleHandler.setFormatter(formatter)
        console_level = logging.getLevelName(console_level.upper())
        consoleHandler.setLevel(console_level)  # Set the level for console output
        log.addHandler(consoleHandler)

    log.propagate = False
    return log
