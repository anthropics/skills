"""
Minimal Finskills HTTP client.

Usage:
    from finskills_client import FinskillsClient
    fs = FinskillsClient()                 # reads FINSKILLS_API_KEY from env
    print(fs.stock_quote("AAPL"))
    print(fs.crypto_price("bitcoin"))

All methods return the parsed `data` field. The full envelope is at `client.last_envelope`.
"""
from __future__ import annotations

import os
import time
import random
from typing import Any, Optional

import requests

DEFAULT_BASE_URL = "https://finskills.net"


class FinskillsError(RuntimeError):
    def __init__(self, status: int, code: str, message: str, body: Any):
        super().__init__(f"[{status} {code}] {message}")
        self.status = status
        self.code = code
        self.message = message
        self.body = body


class FinskillsClient:
    def __init__(
        self,
        api_key: Optional[str] = None,
        base_url: str = DEFAULT_BASE_URL,
        timeout: float = 30.0,
        max_retries: int = 3,
    ):
        self.api_key = api_key or os.environ.get("FINSKILLS_API_KEY")
        if not self.api_key:
            raise RuntimeError(
                "Missing API key. Pass api_key= or set FINSKILLS_API_KEY env var."
            )
        self.base_url = base_url.rstrip("/")
        self.timeout = timeout
        self.max_retries = max_retries
        self.session = requests.Session()
        self.session.headers.update(
            {
                "X-API-Key": self.api_key,
                "Accept": "application/json",
                "User-Agent": "finskills-one-skill/1.0",
            }
        )
        self.last_envelope: dict[str, Any] | None = None

    # ---------------------------------------------------------------- core
    def _get(self, path: str, params: Optional[dict] = None) -> Any:
        url = f"{self.base_url}{path}"
        last_exc: Exception | None = None
        for attempt in range(self.max_retries):
            try:
                r = self.session.get(url, params=params, timeout=self.timeout)
            except requests.RequestException as e:
                last_exc = e
                time.sleep(min(2**attempt + random.random(), 8))
                continue

            if r.status_code == 429 or r.status_code >= 500:
                ra = float(r.headers.get("Retry-After", "0") or 0)
                time.sleep(max(ra, 2**attempt + random.random()))
                continue

            try:
                env = r.json()
            except ValueError:
                raise FinskillsError(r.status_code, "BAD_JSON", r.text[:200], None)

            self.last_envelope = env
            if not r.ok or env.get("success") is False:
                err = env.get("error") or {}
                raise FinskillsError(
                    r.status_code,
                    err.get("code", "ERROR"),
                    err.get("message", "Unknown error"),
                    env,
                )
            return env.get("data", env)
        raise FinskillsError(0, "NETWORK", str(last_exc) if last_exc else "retry exhausted", None)

    # ============================================================ STOCKS
    def stock_quote(self, symbol: str) -> Any:
        return self._get(f"/v1/stocks/quote/{symbol}")

    def stock_quotes(self, symbols: list[str]) -> Any:
        return self._get("/v1/stocks/quotes", {"symbols": ",".join(symbols)})

    def stock_history(self, symbol: str, *, interval: str = "1d", range_: str = "1y", **kw) -> Any:
        return self._get(f"/v1/stocks/history/{symbol}", {"interval": interval, "range": range_, **kw})

    def stock_search(self, q: str, limit: int = 10) -> Any:
        return self._get("/v1/stocks/search", {"q": q, "limit": limit})

    def stock_profile(self, symbol: str) -> Any:
        return self._get(f"/v1/stocks/profile/{symbol}")

    def stock_financials(self, symbol: str, freq: str = "yearly") -> Any:
        return self._get(f"/v1/stocks/financials/{symbol}", {"freq": freq})

    def stock_dividends(self, symbol: str) -> Any:
        return self._get(f"/v1/stocks/dividends/{symbol}")

    def stock_options(self, symbol: str, date: Optional[str] = None) -> Any:
        return self._get(f"/v1/stocks/options/{symbol}", {"date": date} if date else None)

    def stock_holders(self, symbol: str) -> Any:
        return self._get(f"/v1/stocks/holders/{symbol}")

    def stock_recommendations(self, symbol: str) -> Any:
        return self._get(f"/v1/stocks/recommendations/{symbol}")

    def stock_earnings(self, symbol: str) -> Any:
        return self._get(f"/v1/stocks/earnings/{symbol}")

    # ============================================================ CRYPTO
    def crypto_price(self, coin_id: str, vs_currency: str = "usd") -> Any:
        return self._get(f"/v1/free/crypto/price/{coin_id}", {"vs_currency": vs_currency})

    def crypto_markets(self, vs_currency: str = "usd", limit: int = 20, page: int = 1) -> Any:
        return self._get(
            "/v1/free/crypto/markets",
            {"vs_currency": vs_currency, "limit": limit, "page": page},
        )

    def crypto_history(self, coin_id: str, days: int | str = 30, vs_currency: str = "usd") -> Any:
        return self._get(
            f"/v1/free/crypto/history/{coin_id}", {"days": days, "vs_currency": vs_currency}
        )

    # ============================================================= FOREX
    def forex_rates(self, base: str = "USD", symbols: Optional[list[str]] = None) -> Any:
        params = {"base": base}
        if symbols:
            params["symbols"] = ",".join(symbols)
        return self._get("/v1/free/forex/rates", params)

    def forex_history(self, base: str, target: str, start: str, end: str) -> Any:
        return self._get(
            "/v1/free/forex/history",
            {"base": base, "target": target, "start": start, "end": end},
        )

    # ============================================================== MACRO
    def macro_gdp_free(self, country: Optional[str] = None) -> Any:
        if country:
            return self._get(f"/v1/free/macro/gdp/{country}")
        return self._get("/v1/free/macro/gdp")

    def macro_indicator_free(self, code: str) -> Any:
        return self._get(f"/v1/free/macro/indicator/{code}")

    def macro_treasury_rates(self) -> Any:
        return self._get("/v1/free/macro/treasury-rates")

    def macro_inflation_free(self, country: str = "US") -> Any:
        return self._get("/v1/free/macro/inflation", {"country": country})

    def macro_fred(self, series: str) -> Any:
        return self._get(f"/v1/macro/indicator/{series}")

    def macro_interest_rates(self) -> Any:
        return self._get("/v1/macro/interest-rates")

    # ============================================================= MARKET
    def market_summary(self) -> Any:
        return self._get("/v1/market/summary")

    def market_sectors(self, free: bool = True) -> Any:
        return self._get(f"/v1/{'free/' if free else ''}market/sectors")

    def market_indices(self, free: bool = True) -> Any:
        return self._get(f"/v1/{'free/' if free else ''}market/indices")

    def market_top_gainers(self, count: int = 25, free: bool = True) -> Any:
        return self._get(f"/v1/{'free/' if free else ''}market/top-gainers", {"count": count})

    def market_top_losers(self, count: int = 25, free: bool = True) -> Any:
        return self._get(f"/v1/{'free/' if free else ''}market/top-losers", {"count": count})

    def market_most_active(self, count: int = 25) -> Any:
        return self._get("/v1/free/market/most-active", {"count": count})

    def market_advance_decline(self, free: bool = True) -> Any:
        return self._get(f"/v1/{'free/' if free else ''}market/advance-decline")

    def market_fear_greed(self, free: bool = True) -> Any:
        return self._get(f"/v1/{'free/' if free else ''}market/fear-greed")

    def market_vix(self) -> Any:
        return self._get("/v1/free/market/vix")

    def market_movers(self, count: int = 25, free: bool = True) -> Any:
        return self._get(f"/v1/{'free/' if free else ''}market/movers", {"count": count})

    def market_news(self, limit: int = 20, free: bool = True) -> Any:
        return self._get(f"/v1/{'free/' if free else ''}market/news", {"limit": limit})

    def market_breadth(self) -> Any:
        return self._get("/v1/free/market/breadth")

    def market_short_volume(self, symbol: str) -> Any:
        return self._get(f"/v1/free/market/short-volume/{symbol}")

    def market_short_volume_top(self) -> Any:
        return self._get("/v1/free/market/short-volume-top")

    def earnings_calendar(self, date: Optional[str] = None) -> Any:
        return self._get("/v1/free/market/earnings-calendar", {"date": date} if date else None)

    def fama_french(self, model: str = "3factor", freq: str = "daily") -> Any:
        return self._get("/v1/free/market/fama-french", {"model": model, "freq": freq})

    # =============================================================== NEWS
    def news_finance(self, limit: int = 20) -> Any:
        return self._get("/v1/free/news/finance", {"limit": limit})

    def news_latest(self, limit: int = 20) -> Any:
        return self._get("/v1/news/latest", {"limit": limit})

    def news_by_symbol(self, symbol: str, limit: int = 10) -> Any:
        return self._get(f"/v1/news/by-symbol/{symbol}", {"limit": limit})

    # ================================================================ SEC
    def sec_filings(self, cik: str, type_: Optional[str] = None, limit: int = 20) -> Any:
        params = {"limit": limit}
        if type_:
            params["type"] = type_
        return self._get(f"/v1/free/sec/filings/{cik}", params)

    def sec_company_facts(self, cik: str) -> Any:
        return self._get(f"/v1/free/sec/company-facts/{cik}")

    def sec_insider_trades(self, symbol: str) -> Any:
        return self._get(f"/v1/free/sec/insider-trades/{symbol}")

    def sec_insider_summary(self, symbol: str) -> Any:
        return self._get(f"/v1/free/sec/insider-summary/{symbol}")

    def sec_ownership(self, symbol: str) -> Any:
        return self._get(f"/v1/free/sec/ownership/{symbol}")

    # ================================================== ANALYST / ALT-DATA
    def analyst_ratings(self, symbol: str) -> Any:
        return self._get(f"/v1/free/stocks/analyst-ratings/{symbol}")

    def analyst_rating_summary(self, symbol: str) -> Any:
        return self._get(f"/v1/free/stocks/analyst-rating-summary/{symbol}")

    def analyst_estimates(self, symbol: str) -> Any:
        return self._get(f"/v1/free/stocks/estimates/{symbol}")

    def congress_trades(self, symbol: Optional[str] = None, limit: int = 50) -> Any:
        params: dict[str, Any] = {"limit": limit}
        if symbol:
            params["symbol"] = symbol
        return self._get("/v1/free/stocks/congress-trades", params)

    def insider_trades(self, symbol: str) -> Any:
        return self._get(f"/v1/free/stocks/insider-trades/{symbol}")

    def wsb_sentiment(self, symbol: str) -> Any:
        return self._get(f"/v1/free/stocks/wsb-sentiment/{symbol}")

    # ================================================================ ETF
    def etf_list(self) -> Any:
        return self._get("/v1/free/etf/list")

    def etf_holdings(self, symbol: str) -> Any:
        return self._get(f"/v1/free/etf/holdings/{symbol}")

    def index_constituents(self, index: str) -> Any:
        return self._get(f"/v1/free/index/{index}/constituents")

    # ========================================================== COMMODITY
    def commodity_catalog(self, category: Optional[str] = None) -> Any:
        return self._get("/v1/free/commodity/catalog", {"category": category} if category else None)

    def commodity_prices(self, category: Optional[str] = None) -> Any:
        return self._get("/v1/free/commodity/prices", {"category": category} if category else None)

    def commodity_price(self, symbol: str) -> Any:
        return self._get(f"/v1/free/commodity/price/{symbol}")

    def commodity_history(self, symbol: str, range_: str = "1y", interval: str = "1d") -> Any:
        return self._get(
            f"/v1/free/commodity/history/{symbol}", {"range": range_, "interval": interval}
        )

    def commodity_fred_list(self) -> Any:
        return self._get("/v1/free/commodity/fred")

    def commodity_fred(self, series_id: str, **kw) -> Any:
        return self._get(f"/v1/free/commodity/fred/{series_id}", kw or None)

    def commodity_imf_list(self) -> Any:
        return self._get("/v1/free/commodity/imf")

    def commodity_imf_batch(self, indicators: list[str]) -> Any:
        return self._get("/v1/free/commodity/imf/batch", {"indicators": ",".join(indicators)})

    def commodity_imf(self, indicator: str, periods: int = 120) -> Any:
        return self._get(f"/v1/free/commodity/imf/{indicator}", {"periods": periods})

    def commodity_bdi(self) -> Any:
        return self._get("/v1/free/commodity/bdi")

    def commodity_bdi_history(self, range_: str = "1y") -> Any:
        return self._get("/v1/free/commodity/bdi/history", {"range": range_})

    # ============================================================== OTHER
    def banking_search(self, q: str, state: Optional[str] = None, limit: int = 20) -> Any:
        params: dict[str, Any] = {"q": q, "limit": limit}
        if state:
            params["state"] = state
        return self._get("/v1/free/banking/search", params)

    def bin_lookup(self, bin_: str) -> Any:
        return self._get(f"/v1/free/payment/bin/{bin_}")

    def fema_disasters(self, **kw) -> Any:
        return self._get("/v1/free/fema/disasters", kw or None)


if __name__ == "__main__":
    import json, sys

    fs = FinskillsClient()
    sym = sys.argv[1] if len(sys.argv) > 1 else "AAPL"
    print(json.dumps(fs.stock_quote(sym), indent=2))
