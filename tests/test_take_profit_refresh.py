from datetime import datetime, timedelta
from types import SimpleNamespace

from directionalscalper.core.exchanges.bybit import BybitExchange
from directionalscalper.core.strategies.bybit.bybit_strategy import BybitStrategy


def tp_order(order_id, side="sell", qty=100, price=10.2):
    return {
        "id": order_id,
        "side": side,
        "price": price,
        "info": {
            "qty": str(qty),
            "reduceOnly": True,
            "orderLinkId": "",
        },
    }


class DummyTpExchange:
    def __init__(self, fresh_orders=None):
        self.fresh_orders = fresh_orders or []
        self.canceled = []
        self.created = []
        self.parser = object.__new__(BybitExchange)

    def get_open_tp_orders(self, open_orders):
        return BybitExchange.get_open_tp_orders(self.parser, open_orders)

    def get_open_orders(self, symbol):
        return list(self.fresh_orders)

    def cancel_order_by_id(self, order_id, symbol):
        self.canceled.append((order_id, symbol))

    def get_current_price(self, symbol):
        return 9.5

    def get_orderbook(self, symbol):
        return {"asks": [[10.3, 1]], "bids": [[9.4, 1]]}

    def create_take_profit_order_bybit(self, symbol, order_type, side, amount, price, positionIdx=1, reduce_only=True):
        order = {
            "id": f"created-{len(self.created) + 1}",
            "symbol": symbol,
            "type": order_type,
            "side": side,
            "amount": amount,
            "price": price,
            "positionIdx": positionIdx,
            "reduce_only": reduce_only,
        }
        self.created.append(order)
        return order

    def create_normal_take_profit_order_bybit(self, *args, **kwargs):
        return self.create_take_profit_order_bybit(*args, **kwargs)


def tp_strategy(exchange):
    strategy = object.__new__(BybitStrategy)
    strategy.config = SimpleNamespace(linear_grid={"grid_behavior": "xgridt"})
    strategy.exchange = exchange
    strategy.auto_reduce_order_ids = {}
    strategy.recent_tp_placements = {}
    strategy.last_known_ask = {}
    strategy.last_known_bid = {}
    strategy.retry_api_call = lambda function, *args, **kwargs: function(*args, **kwargs)
    strategy.min_notional = lambda symbol: 1
    strategy.calculate_quickscalp_short_take_profit_dynamic_distance = lambda *args, **kwargs: (9.8, 9.7)
    strategy.calculate_quickscalp_long_take_profit_dynamic_distance = lambda *args, **kwargs: (10.1, 10.2)
    strategy.calculate_next_update_time = lambda: datetime.now() + timedelta(seconds=10)
    return strategy


def test_tp_update_replaces_mismatched_order_after_refresh():
    stale_orders = [tp_order("old-small", qty=50)]
    exchange = DummyTpExchange(fresh_orders=stale_orders)
    strategy = tp_strategy(exchange)

    strategy.update_quickscalp_tp_dynamic(
        symbol="IRYSUSDT",
        pos_qty=100,
        upnl_profit_pct=0.01,
        max_upnl_profit_pct=0.02,
        short_pos_price=0,
        long_pos_price=10,
        positionIdx=1,
        order_side="sell",
        last_tp_update=datetime.now() - timedelta(seconds=1),
        tp_order_counts={"long_tp_count": 1, "short_tp_count": 0},
        open_orders=stale_orders,
    )

    assert exchange.canceled == [("old-small", "IRYSUSDT")]
    assert len(exchange.created) == 1
    assert exchange.created[0]["amount"] == 100
    assert exchange.created[0]["price"] == 10.2


def test_tp_update_uses_fresh_matching_order_before_creating_duplicate():
    exchange = DummyTpExchange(fresh_orders=[tp_order("existing", qty=100)])
    strategy = tp_strategy(exchange)

    strategy.update_quickscalp_tp_dynamic(
        symbol="IRYSUSDT",
        pos_qty=100,
        upnl_profit_pct=0.01,
        max_upnl_profit_pct=0.02,
        short_pos_price=0,
        long_pos_price=10,
        positionIdx=1,
        order_side="sell",
        last_tp_update=datetime.now() - timedelta(seconds=1),
        tp_order_counts={"long_tp_count": 0, "short_tp_count": 0},
        open_orders=[],
    )

    assert exchange.canceled == []
    assert exchange.created == []


def test_tp_update_suppresses_immediate_duplicate_after_recent_create():
    exchange = DummyTpExchange(fresh_orders=[])
    strategy = tp_strategy(exchange)
    strategy._record_recent_tp_placement("IRYSUSDT", "sell", 100, 10.2)

    strategy.update_quickscalp_tp_dynamic(
        symbol="IRYSUSDT",
        pos_qty=100,
        upnl_profit_pct=0.01,
        max_upnl_profit_pct=0.02,
        short_pos_price=0,
        long_pos_price=10,
        positionIdx=1,
        order_side="sell",
        last_tp_update=datetime.now() - timedelta(seconds=1),
        tp_order_counts={"long_tp_count": 0, "short_tp_count": 0},
        open_orders=[],
    )

    assert exchange.created == []
