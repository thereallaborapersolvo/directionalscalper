from types import SimpleNamespace

from directionalscalper.core.strategies.bybit.bybit_strategy import BybitStrategy


def strategy_with_ratio(ratio=None):
    strategy = object.__new__(BybitStrategy)
    linear_grid = {}
    if ratio is not None:
        linear_grid["short_exposure_ratio_of_long"] = ratio
    strategy.config = SimpleNamespace(linear_grid=linear_grid)
    return strategy


def test_short_exposure_ratio_clamps_short_limits():
    strategy = strategy_with_ratio(0.5)

    limits = strategy.resolve_short_exposure_limits(
        wallet_exposure_limit_long=0.010,
        wallet_exposure_limit_short=0.006,
        max_qty_percent_long=60,
        max_qty_percent_short=60,
        max_usd_position_value_long=None,
        max_usd_position_value_short=None,
    )

    assert limits["wallet_exposure_limit_short"] == 0.005
    assert limits["max_qty_percent_short"] == 30
    assert limits["max_usd_position_value_short"] is None


def test_short_exposure_ratio_does_not_raise_lower_short_limits():
    strategy = strategy_with_ratio(0.5)

    limits = strategy.resolve_short_exposure_limits(
        wallet_exposure_limit_long=0.010,
        wallet_exposure_limit_short=0.003,
        max_qty_percent_long=60,
        max_qty_percent_short=20,
        max_usd_position_value_long=None,
        max_usd_position_value_short=None,
    )

    assert limits["wallet_exposure_limit_short"] == 0.003
    assert limits["max_qty_percent_short"] == 20


def test_short_exposure_ratio_defaults_to_backward_compatible_value():
    strategy = strategy_with_ratio()

    limits = strategy.resolve_short_exposure_limits(
        wallet_exposure_limit_long=0.010,
        wallet_exposure_limit_short=0.006,
        max_qty_percent_long=60,
        max_qty_percent_short=60,
        max_usd_position_value_long=None,
        max_usd_position_value_short=None,
    )

    assert limits["short_exposure_ratio_of_long"] == 1.0
    assert limits["wallet_exposure_limit_short"] == 0.006
    assert limits["max_qty_percent_short"] == 60


def test_short_usd_cap_derives_from_long_usd_cap():
    strategy = strategy_with_ratio(0.5)

    limits_without_short_cap = strategy.resolve_short_exposure_limits(
        wallet_exposure_limit_long=0.010,
        wallet_exposure_limit_short=0.006,
        max_qty_percent_long=60,
        max_qty_percent_short=60,
        max_usd_position_value_long=1000,
        max_usd_position_value_short=None,
    )
    limits_with_lower_short_cap = strategy.resolve_short_exposure_limits(
        wallet_exposure_limit_long=0.010,
        wallet_exposure_limit_short=0.006,
        max_qty_percent_long=60,
        max_qty_percent_short=60,
        max_usd_position_value_long=1000,
        max_usd_position_value_short=300,
    )

    assert limits_without_short_cap["max_usd_position_value_short"] == 500
    assert limits_with_lower_short_cap["max_usd_position_value_short"] == 300
