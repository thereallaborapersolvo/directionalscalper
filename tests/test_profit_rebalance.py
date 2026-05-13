import json
import inspect
from types import SimpleNamespace

from directionalscalper.core.exchanges.bybit import BybitExchange
from directionalscalper.core.strategies.bybit.bybit_strategy import BybitStrategy


class DummyExchange:
    def __init__(self):
        self.orders = []
        self.canceled = []

    def create_tagged_limit_order_bybit(
        self,
        symbol,
        side,
        qty,
        price,
        positionIdx=0,
        isLeverage=False,
        orderLinkId=None,
        postOnly=True,
        params=None,
    ):
        order = {
            "id": f"order-{len(self.orders) + 1}",
            "symbol": symbol,
            "side": side,
            "amount": qty,
            "price": price,
            "info": {
                "orderLinkId": orderLinkId,
                "positionIdx": positionIdx,
                "reduceOnly": (params or {}).get("reduceOnly", False),
                "postOnly": postOnly,
            },
        }
        self.orders.append(order)
        return order

    def cancel_order_by_id(self, order_id, symbol):
        self.canceled.append((order_id, symbol))


def strategy(tmp_path):
    strategy = object.__new__(BybitStrategy)
    state_path = tmp_path / "profit_rebalance_state.json"
    strategy.config = SimpleNamespace(
        shared_data_path=str(tmp_path),
        linear_grid={
            "profit_rebalance_enabled": True,
            "profit_rebalance_loss_budget_ratio": 0.5,
            "profit_rebalance_min_daily_profit_usd": 0.20,
            "profit_rebalance_max_position_close_pct": 0.05,
            "profit_rebalance_order_ttl_seconds": 600,
            "profit_rebalance_state_path": str(state_path),
            "profit_rebalance_order_prefix": "PRB",
        },
    )
    strategy.exchange = DummyExchange()
    return strategy


def test_profit_rebalance_initializes_fresh_daily_baseline(tmp_path):
    s = strategy(tmp_path)
    state = {"version": 1, "symbols": {}}

    symbol_state, initialized = s.ensure_profit_rebalance_symbol_state(
        state,
        "XRPUSDT",
        current_cum_realized=17.0,
        day_key="2026-05-13",
    )

    assert initialized is True
    assert symbol_state["baseline_cum_realized"] == 17.0
    assert symbol_state["loss_spent"] == 0.0
    assert symbol_state["active_order"] is None


def test_profit_rebalance_budget_offsets_rebalance_loss_spent(tmp_path):
    s = strategy(tmp_path)
    symbol_state = {
        "baseline_cum_realized": 100.0,
        "loss_spent": 0.10,
        "reserved_loss": 0.0,
    }

    budget = s.calculate_profit_rebalance_budget(
        symbol_state,
        current_cum_realized=100.20,
        loss_budget_ratio=0.5,
    )

    assert round(budget["source_profit_today"], 8) == 0.30
    assert round(budget["total_loss_budget"], 8) == 0.15
    assert round(budget["available_loss_budget"], 8) == 0.05


def test_profit_rebalance_close_respects_budget_and_position_slice(tmp_path):
    s = strategy(tmp_path)

    close = s.calculate_profit_rebalance_close(
        side="short",
        position_qty=100,
        position_price=10.00,
        current_price=10.01,
        side_upnl=-1.0,
        available_loss_budget=0.15,
        max_position_close_pct=0.05,
        qty_step=1,
        min_qty=1,
        min_notional_value=6,
    )

    assert close["reason"] == "ok"
    assert close["qty"] == 5
    assert round(close["estimated_loss"], 8) == 0.05


def test_profit_rebalance_close_skips_when_min_order_exceeds_budget(tmp_path):
    s = strategy(tmp_path)

    close = s.calculate_profit_rebalance_close(
        side="long",
        position_qty=100,
        position_price=10.00,
        current_price=9.00,
        side_upnl=-100,
        available_loss_budget=0.15,
        max_position_close_pct=0.05,
        qty_step=1,
        min_qty=1,
        min_notional_value=6,
    )

    assert close["qty"] == 0.0
    assert close["reason"] == "budget_below_min_order"


def test_profit_rebalance_places_passive_reduce_only_order_for_blocked_short(tmp_path):
    s = strategy(tmp_path)
    day = s.profit_rebalance_day_key()
    state_path = s.get_profit_rebalance_config()["state_path"]
    with open(state_path, "w") as f:
        json.dump(
            {
                "version": 1,
                "symbols": {
                    "TESTUSDT": {
                        "day": day,
                        "baseline_cum_realized": 100.0,
                        "loss_spent": 0.0,
                        "reserved_loss": 0.0,
                        "active_order": None,
                    }
                },
            },
            f,
        )

    result = s.maybe_profit_rebalance_stuck_position(
        symbol="TESTUSDT",
        current_cum_realized=100.30,
        long_pos_qty=0,
        short_pos_qty=100,
        long_pos_price=0,
        short_pos_price=10.00,
        long_upnl=0,
        short_upnl=-1.0,
        current_price=10.01,
        best_ask_price=10.02,
        best_bid_price=10.00,
        qty_step=1,
        min_qty=1,
        long_blocked=False,
        short_blocked=True,
        open_orders=[],
    )

    assert result["action"] == "order_placed"
    assert result["side"] == "short"
    assert s.exchange.orders[0]["side"] == "buy"
    assert s.exchange.orders[0]["price"] == 10.00
    assert s.exchange.orders[0]["info"]["positionIdx"] == 2
    assert s.exchange.orders[0]["info"]["reduceOnly"] is True
    assert s.exchange.orders[0]["info"]["postOnly"] is True
    assert s.exchange.orders[0]["info"]["orderLinkId"].startswith("PRB-")


def test_profit_rebalance_reconciles_filled_active_order(tmp_path):
    s = strategy(tmp_path)
    symbol_state = {
        "loss_spent": 0.0,
        "reserved_loss": 0.05,
        "active_order": {
            "id": "order-1",
            "side": "short",
            "qty": 5,
            "estimated_loss": 0.05,
            "position_qty_at_order": 100,
            "created_at": 1,
        },
    }

    active = s.reconcile_profit_rebalance_active_order(
        symbol_state,
        symbol="TESTUSDT",
        open_orders=[],
        current_long_qty=0,
        current_short_qty=95,
        order_ttl_seconds=600,
        prefix="PRB",
        now_ts=2,
    )

    assert active is False
    assert symbol_state["active_order"] is None
    assert symbol_state["reserved_loss"] == 0.0
    assert symbol_state["loss_spent"] == 0.05


def test_tp_filter_ignores_profit_rebalance_orders():
    exchange = object.__new__(BybitExchange)
    open_orders = [
        {
            "id": "tp-1",
            "side": "sell",
            "price": 10.2,
            "info": {"qty": "5", "reduceOnly": True, "orderLinkId": "TP-1"},
        },
        {
            "id": "prb-1",
            "side": "sell",
            "price": 10.0,
            "info": {"qty": "5", "reduceOnly": True, "orderLinkId": "PRB-TEST-L-1"},
        },
    ]

    long_tp_orders, short_tp_orders = exchange.get_open_tp_orders(open_orders)

    assert [order["id"] for order in long_tp_orders] == ["tp-1"]
    assert short_tp_orders == []


def test_grid_dispatch_accepts_profit_rebalance_inputs():
    lineargrid_sig = inspect.signature(BybitStrategy.lineargrid_base)
    handle_sig = inspect.signature(BybitStrategy.handle_grid_trades)

    for param in (
        "cum_realised_pnl_long",
        "cum_realised_pnl_short",
        "long_upnl",
        "short_upnl",
    ):
        assert param in lineargrid_sig.parameters
        assert param in handle_sig.parameters
