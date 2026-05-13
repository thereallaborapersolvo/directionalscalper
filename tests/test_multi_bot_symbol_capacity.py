from types import SimpleNamespace

import multi_bot_aio as bot


class AliveThread:
    def is_alive(self):
        return True


class DoneEvent:
    def __init__(self, done=False):
        self.done = done

    def is_set(self):
        return self.done


class DummyMarketMaker:
    def __init__(self, signal):
        self.signal = signal
        self.manager = None

    def get_signal(self, symbol):
        return self.signal


def reset_capacity_state(monkeypatch):
    bot.active_symbols = set()
    bot.active_long_symbols = set()
    bot.active_short_symbols = set()
    bot.unique_active_symbols = set()
    bot.pending_entry_symbols = set()
    bot.long_threads = {}
    bot.short_threads = {}
    monkeypatch.setattr(bot, "is_long_position", lambda symbol: symbol in {"XRPUSDT", "UNIUSDT"})
    monkeypatch.setattr(bot, "is_short_position", lambda symbol: False)


def test_update_active_symbols_keeps_live_thread_capacity(monkeypatch):
    reset_capacity_state(monkeypatch)
    bot.long_threads = {"JTOUSDT": (AliveThread(), DoneEvent())}

    bot.update_active_symbols({"XRPUSDT", "UNIUSDT"})

    assert bot.unique_active_symbols == {"XRPUSDT", "UNIUSDT", "JTOUSDT"}
    assert "JTOUSDT" in bot.active_long_symbols


def test_process_signal_releases_neutral_pending_reservation(monkeypatch):
    reset_capacity_state(monkeypatch)
    bot.reserve_pending_entry_symbol("DOTUSDT")

    action_taken = bot.process_signal(
        "DOTUSDT",
        args=SimpleNamespace(),
        market_maker=DummyMarketMaker("neutral"),
        manager=SimpleNamespace(),
        symbols_allowed=3,
        open_position_data=[],
        is_open_position=False,
        long_mode=True,
        short_mode=True,
        graceful_stop_long=False,
        graceful_stop_short=False,
    )

    assert action_taken is False
    assert "DOTUSDT" not in bot.pending_entry_symbols
    assert "DOTUSDT" not in bot.unique_active_symbols


def test_handle_signal_blocks_new_symbol_when_live_thread_fills_capacity(monkeypatch):
    reset_capacity_state(monkeypatch)
    bot.long_threads = {"JTOUSDT": (AliveThread(), DoneEvent())}
    bot.active_long_symbols = {"XRPUSDT", "UNIUSDT", "JTOUSDT"}
    bot.unique_active_symbols = {"XRPUSDT", "UNIUSDT", "JTOUSDT"}
    started = []
    monkeypatch.setattr(bot, "start_thread_for_symbol", lambda *args, **kwargs: started.append(args[0]) or True)

    action_taken = bot.handle_signal(
        "WIFUSDT",
        args=SimpleNamespace(),
        manager=SimpleNamespace(),
        signal="long",
        open_position_data=[
            {"symbol": "XRPUSDT", "side": "long", "contracts": 1},
            {"symbol": "UNIUSDT", "side": "long", "contracts": 1},
        ],
        symbols_allowed=3,
        is_open_position=False,
        long_mode=True,
        short_mode=True,
        graceful_stop_long=False,
        graceful_stop_short=False,
        max_side_positions_allowed=6,
    )

    assert action_taken is False
    assert started == []


def test_handle_signal_allows_reserved_symbol_to_use_final_slot(monkeypatch):
    reset_capacity_state(monkeypatch)
    bot.active_long_symbols = {"XRPUSDT", "UNIUSDT"}
    bot.unique_active_symbols = {"XRPUSDT", "UNIUSDT"}
    bot.reserve_pending_entry_symbol("WIFUSDT")
    started = []
    monkeypatch.setattr(bot, "start_thread_for_symbol", lambda *args, **kwargs: started.append(args[0]) or True)

    action_taken = bot.handle_signal(
        "WIFUSDT",
        args=SimpleNamespace(),
        manager=SimpleNamespace(),
        signal="long",
        open_position_data=[
            {"symbol": "XRPUSDT", "side": "long", "contracts": 1},
            {"symbol": "UNIUSDT", "side": "long", "contracts": 1},
        ],
        symbols_allowed=3,
        is_open_position=False,
        long_mode=True,
        short_mode=True,
        graceful_stop_long=False,
        graceful_stop_short=False,
        max_side_positions_allowed=6,
    )

    assert action_taken is True
    assert started == ["WIFUSDT"]
