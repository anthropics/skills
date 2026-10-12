#!/usr/bin/env python3
"""
APIClaw CLI — Amazon Product Research via APIClaw API

Single-script interface for all 5 APIClaw endpoints + composite workflows.
Handles authentication, retries, rate limits, parameter quirks, and output formatting.

Usage:
    python apiclaw.py categories --keyword "pet supplies"
    python apiclaw.py market --category "Pet Supplies" --topn 10
    python apiclaw.py products --keyword "yoga mat" --mode beginner
    python apiclaw.py competitors --keyword "wireless earbuds"
    python apiclaw.py product --asin B09V3KXJPB
    python apiclaw.py analyze --asin B09V3KXJPB --label-type painPoints
    python apiclaw.py report --keyword "pet supplies"
    python apiclaw.py opportunity --keyword "pet supplies"

Environment:
    APICLAW_API_KEY — Required. Get one at https://apiclaw.io/api-keys
"""

import argparse
import json
import os
import sys
import time
import urllib.request
import urllib.error

# ─── Configuration ───────────────────────────────────────────────────────────

BASE_URL = "https://api.apiclaw.io/openapi/v2"  # APIClaw API base URL
API_DOCS = "https://api.apiclaw.io/api-docs"   # API documentation URL
MAX_RETRIES = 2       # Maximum number of retry attempts for failed requests
RETRY_DELAY = 2       # Initial retry delay in seconds; doubles on 429 (rate limit)
REQUEST_TIMEOUT = 60  # Request timeout in seconds; realtime/product can be slow (up to 30s)

# 14 built-in product selection modes
# Each maps to a set of products/search filter parameters
PRODUCT_MODES = {
    "fast-movers":              {"monthlySalesMin": 300, "salesGrowthRateMin": 0.1},
    "emerging":                 {"monthlySalesMax": 600, "salesGrowthRateMin": 0.1, "listingAge": "180"},
    "single-variant":           {"salesGrowthRateMin": 0.2, "variantCountMax": 1, "listingAge": "180"},
    "high-demand-low-barrier":  {"monthlySalesMin": 300, "reviewCountMax": 50, "listingAge": "180"},
    "long-tail":                {"bsrMin": 10000, "bsrMax": 50000, "priceMax": 30, "sellerCountMax": 1, "monthlySalesMax": 300},
    "underserved":              {"monthlySalesMin": 300, "ratingMax": 3.7, "listingAge": "180"},
    "new-release":              {"monthlySalesMax": 500, "badges": ["New Release"], "fulfillment": ["FBA", "FBM"]},
    "fbm-friendly":             {"monthlySalesMin": 300, "fulfillment": ["FBM"], "listingAge": "180"},
    "low-price":                {"priceMax": 10},
    "broad-catalog":            {"bsrGrowthRateMin": 0.99, "reviewCountMax": 10, "listingAge": "90"},
    "selective-catalog":        {"bsrGrowthRateMin": 0.99, "listingAge": "90"},
    "speculative":              {"monthlySalesMin": 600, "sellerCountMin": 3, "listingAge": "180"},
    "beginner":                 {"monthlySalesMin": 300, "priceMin": 15, "priceMax": 60, "fulfillment": ["FBA"],
                                 "salesGrowthRateMin": 0.03, "listingAge": "365",
                                 "excludeKeywords": "Brow,Air Fryer,Body Fragrance Mist,Ornament,Ivory,Bed Comforter,Biker Shorts,Mens Dress Shoe,Charms,Dumbbell,Gaming Chair,Skipping Rope,Hoops,Plus Hoola,Kids Bike Helmet,Socks,Cushion,Camping Hammock,Double Leggings,Yoga,Hand Warmers,Trail Camera,Water Bottle,Insulated Food,Pillow,Pillows,iPhone,Dog Bark Collar,Leg Covers,Leg Cover,Laptop Stand,Pet Briefs,Brief,Hangers,Hanger,Slip Rug Pad,rossbody,Fanny Pack,Bedding,Dog Harness,Sweet Water Decor,Eyeshadow,Cotton Sleepsack,Swaddle,Chocolate Bra,Wireless Bed Sheet Set,Car Windshield Curtain,Curtains,Wallet,Green Tea,Picture Frame,Womens,Women Fan,Bottle,Essential Oil,Tumbler,YETI,Vitamin,Vitamins,Face Mask,Led Strip,Pocket,Women's Watch,Waffle Case,Gloves,Shorts,Short Yoga,StrawExpert,Wrap Around Pillowcases,Cup,Bath Mats,Bedsure,Pillowcase,Bathroom,Shower,Milk Frother,Masks,Bug Zapper,Touchless Thermometer,Cat Litter Mat,Probiotics,Smart Plug,Natural Vitality Bottle,Christmas,Sleeveless,Shape Shifting Box,Refrigerator Organizer,Hydration Multiplier,Standard Mouth,Gift Box,USB C,Superhero,Digital Caliper,Massage Gun,Fidget Toys,Garden Hose,Cookie,Blanket,Protein Bars,Caramel Cashew,String Lights,Umbrella,Wearable Blanket,Diapers,Halloween,Flying Toys,Laundry Basket,Kitchen Faucet,Citrulline Malate,Onesie,Pajamas,Nail Polish Kit,fairy finder,Allergy,Immune Supplement,Frying Pan,Tablecloth,Electric Knife,Butter Dish,Dancing Cactus,Maya Mint,ice Cream,Christmas Tree,Liquid Motion Lamp,Stuffed Animal,Plush Bed Comforter,Journal,Women's,Sleeveless Wrap,Supplement,Screen Magnifier,Foot Massager,Machine,Santa,Anime Heroes,Air Mattress,Three Barrel Curling,3D Printer Filament,Power Strip,Rechargeable Toothbrush,Hooded Bathrobe,Sleepwear,Baby Einstein,Vinyl,Plastic Plates,Doorbell,Month Planner,Wooden Balls,Arceus,Wipes,Perfume,Rings,Bore Sight,Fishing Lures,Ear Protection,Firewood Rack,Sling Bag,Resistance Bands,Belt,Backpacks,Silver Slides,Whiteboard,Sports Bra,Cover,Jade Stud,Earrings,Necklace,Snow Shovel,Computer Desk,Dog Pee Pads,Turtleneck,Glasses,Spa,Up Balancer"},
    "top-bsr":                  {"subBsrMax": 1000},
}


# ─── API Client ──────────────────────────────────────────────────────────────

def get_api_key():
    """
    Get API key from environment variable or config file.

    Priority:
    1. Environment variable APICLAW_API_KEY
    2. Config file config.json in the skill directory (next to scripts/)
    """
    # Try environment variable first
    key = os.environ.get("APICLAW_API_KEY", "").strip()
    if key:
        return key

    # Try config file in skill directory (parent of scripts/)
    script_dir = os.path.dirname(os.path.abspath(__file__))
    skill_dir = os.path.dirname(script_dir)  # go up from scripts/ to skill root
    config_path = os.path.join(skill_dir, "config.json")
    if os.path.exists(config_path):
        try:
            with open(config_path, "r", encoding="utf-8") as f:
                config = json.load(f)
                key = config.get("api_key", "").strip()
                if key:
                    return key
        except (json.JSONDecodeError, IOError) as e:
            print(f"WARNING: Failed to read config file: {e}", file=sys.stderr)

    # No key found
    print("ERROR: API Key not found.", file=sys.stderr)
    print("", file=sys.stderr)
    print("Please configure your API Key using one of these methods:", file=sys.stderr)
    print("", file=sys.stderr)
    print("  Method 1: Environment variable (recommended)", file=sys.stderr)
    print("    export APICLAW_API_KEY='hms_live_yourkey'", file=sys.stderr)
    print("", file=sys.stderr)
    print("  Method 2: Config file", file=sys.stderr)
    print(f"    Create config.json in the skill directory: {skill_dir}", file=sys.stderr)
    print('    Content: {"api_key": "hms_live_yourkey"}', file=sys.stderr)
    print("", file=sys.stderr)
    print("Get a free key at https://apiclaw.io/api-keys", file=sys.stderr)
    sys.exit(1)


def api_call(endpoint: str, params: dict) -> dict:
    """
    Make a POST request to APIClaw API with retry and error handling.

    Returns the parsed JSON response on success, with _query metadata injected.
    Exits with a clear error message on failure.
    """
    url = f"{BASE_URL}/{endpoint}"
    api_key = get_api_key()

    # Clean params: remove None values
    params = {k: v for k, v in params.items() if v is not None}

    # Quirk: topN and newProductPeriod must be strings
    for str_field in ("topN", "newProductPeriod"):
        if str_field in params and not isinstance(params[str_field], str):
            params[str_field] = str(params[str_field])

    # Save the actual params sent to API (for _query metadata)
    actual_params = dict(params)

    body = json.dumps(params).encode("utf-8")
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
        "User-Agent": "APIClaw-CLI/1.0 (Python)",
    }

    delay = RETRY_DELAY
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            req = urllib.request.Request(url, data=body, headers=headers, method="POST")
            with urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                if data.get("success"):
                    # Inject _query metadata so AI knows exactly what was sent
                    data["_query"] = {
                        "endpoint": endpoint,
                        "params": actual_params,
                    }
                    # Inject _credits metadata for usage tracking
                    data["_credits"] = {
                        "consumed": data.get("creditsConsumed"),
                        "remaining": data.get("creditsRemaining"),
                    }
                    return data
                else:
                    err = data.get("error", {})
                    print(f"API error: {err.get('code', 'unknown')} — {err.get('message', json.dumps(err))}", file=sys.stderr)
                    sys.exit(1)
        except urllib.error.HTTPError as e:
            status = e.code
            if status == 401:
                return _error_result(401, "API Key invalid or expired",
                    "Check your API Key or get a new one at https://apiclaw.io/api-keys",
                    endpoint, actual_params)
            elif status == 402:
                return _error_result(402, "API quota exhausted or subscription expired",
                    "Check your plan at https://apiclaw.io/api-keys or provide a new Key",
                    endpoint, actual_params)
            elif status == 429:
                if attempt < MAX_RETRIES:
                    print(f"Rate limited (429). Waiting {delay}s before retry {attempt}/{MAX_RETRIES}...", file=sys.stderr)
                    time.sleep(delay)
                    delay *= 2
                    continue
                else:
                    return _error_result(429, "Rate limit exceeded after retries",
                        "Try again later or reduce request frequency",
                        endpoint, actual_params)
            elif status == 404:
                return _error_result(404, f"Endpoint '{endpoint}' not found",
                    f"Check {API_DOCS} for current endpoints",
                    endpoint, actual_params)
            else:
                if attempt < MAX_RETRIES:
                    print(f"HTTP {status}. Retrying {attempt}/{MAX_RETRIES}...", file=sys.stderr)
                    time.sleep(delay)
                    continue
                else:
                    return _error_result(status, f"HTTP {status} after {MAX_RETRIES} attempts",
                        "Check network or try again later",
                        endpoint, actual_params)
        except Exception as e:
            if attempt < MAX_RETRIES:
                print(f"Request failed: {e}. Retrying {attempt}/{MAX_RETRIES}...", file=sys.stderr)
                time.sleep(delay)
                continue
            else:
                return _error_result(0, f"Request failed: {e}",
                    "Check network connection",
                    endpoint, actual_params)

    return _error_result(0, "Unexpected retry loop exit", "This should not happen", endpoint, actual_params)


def _error_result(status: int, message: str, action: str, endpoint: str, params: dict) -> dict:
    """
    Build a structured error result instead of sys.exit().
    This lets AI read the error from JSON stdout and take appropriate action.
    """
    print(f"ERROR: {message}", file=sys.stderr)
    return {
        "success": False,
        "error": {
            "status": status,
            "message": message,
            "action": action,
        },
        "_query": {
            "endpoint": endpoint,
            "params": params,
        },
    }


def output(data, fmt="json"):
    """Print output in the requested format."""
    if fmt == "json":
        print(json.dumps(data, indent=2, ensure_ascii=False))
    elif fmt == "compact":
        print(json.dumps(data, ensure_ascii=False))
    else:
        print(json.dumps(data, indent=2, ensure_ascii=False))


# ─── Helper: parse category string ──────────────────────────────────────────

def parse_category(cat_str: str) -> list:
    """Parse category path string into a list.

    Supported formats (in priority order):
    1. ' > ' separator: 'Pet Supplies > Dogs > Toys'  (recommended, handles commas in names)
    2. ',' separator:   'Pet Supplies,Dogs,Toys'       (legacy, breaks on names with commas)

    Use ' > ' when category names contain commas, e.g.:
    'Baby Products > Baby Care > Pacifiers, Teethers & Teething Relief'
    """
    if not cat_str:
        return []
    # Prefer ' > ' separator — handles commas in category names correctly
    if " > " in cat_str:
        return [c.strip() for c in cat_str.split(" > ")]
    return [c.strip() for c in cat_str.split(",")]


# ─── Subcommands ─────────────────────────────────────────────────────────────

def cmd_categories(args):
    """Query the Amazon category tree."""
    params = {}
    if args.keyword:
        params["categoryKeyword"] = args.keyword
    elif args.category:
        params["categoryPath"] = parse_category(args.category)
    elif args.parent:
        params["parentCategoryPath"] = parse_category(args.parent)
    # else: no params → root categories

    result = api_call("categories", params)
    output(result, args.format)


def cmd_market(args):
    """Search market-level aggregate data for a category."""
    params = {}
    if args.category:
        params["categoryPath"] = parse_category(args.category)
    if args.keyword:
        params["categoryKeyword"] = args.keyword
    if args.topn:
        params["topN"] = str(args.topn)
    if args.page_size:
        params["pageSize"] = args.page_size
    if args.sort:
        params["sortBy"] = args.sort
    if args.order:
        params["sortOrder"] = args.order

    result = api_call("markets/search", params)
    output(result, args.format)


def cmd_products(args):
    """Search products with filters (product selection / 选品)."""
    params = {}
    if args.keyword:
        params["keyword"] = args.keyword
    if args.category:
        params["categoryPath"] = parse_category(args.category)

    # Apply mode preset filters
    if args.mode:
        mode_key = args.mode.lower().replace(" ", "-").replace("_", "-")
        if mode_key in PRODUCT_MODES:
            params.update(PRODUCT_MODES[mode_key])
        else:
            print(f"ERROR: Unknown mode '{args.mode}'.", file=sys.stderr)
            print(f"Available modes: {', '.join(sorted(PRODUCT_MODES.keys()))}", file=sys.stderr)
            sys.exit(1)

    # Override with explicit filters
    for attr in ("monthlySalesMin", "monthlySalesMax", "reviewCountMin", "reviewCountMax",
                 "priceMin", "priceMax", "ratingMin", "ratingMax", "bsrMin", "bsrMax",
                 "salesGrowthRateMin", "salesGrowthRateMax", "sellerCountMin", "sellerCountMax",
                 "variantCountMin", "variantCountMax"):
        val = getattr(args, attr.replace("Min", "_min").replace("Max", "_max")
                      .replace("monthly", "monthly_").replace("review", "review_")
                      .replace("sales", "sales_").replace("Growth", "_growth_")
                      .replace("Rate", "rate_").replace("price", "price_")
                      .replace("rating", "rating_").replace("bsr", "bsr_")
                      .replace("seller", "seller_").replace("Count", "_count_")
                      .replace("variant", "variant_"), None)
        # Simplified: just use the argparse names directly

    if args.sales_min is not None:
        params["monthlySalesMin"] = args.sales_min
    if args.sales_max is not None:
        params["monthlySalesMax"] = args.sales_max
    if args.reviews_min is not None:
        params["reviewCountMin"] = args.reviews_min
    if args.reviews_max is not None:
        params["reviewCountMax"] = args.reviews_max
    if args.price_min is not None:
        params["priceMin"] = args.price_min
    if args.price_max is not None:
        params["priceMax"] = args.price_max
    if args.rating_min is not None:
        params["ratingMin"] = args.rating_min
    if args.rating_max is not None:
        params["ratingMax"] = args.rating_max
    if args.growth_min is not None:
        params["salesGrowthRateMin"] = args.growth_min
    if args.bsr_min is not None:
        params["bsrMin"] = args.bsr_min
    if args.bsr_max is not None:
        params["bsrMax"] = args.bsr_max
    if args.seller_count_min is not None:
        params["sellerCountMin"] = args.seller_count_min
    if args.seller_count_max is not None:
        params["sellerCountMax"] = args.seller_count_max
    if args.variant_count_max is not None:
        params["variantCountMax"] = args.variant_count_max
    if args.keyword_match_type:
        params["keywordMatchType"] = args.keyword_match_type
    if args.sub_bsr_max is not None:
        params["subBsrMax"] = args.sub_bsr_max
    if args.exclude_keywords:
        params["excludeKeywords"] = args.exclude_keywords
    if args.listing_age:
        params["listingAge"] = args.listing_age
    if args.badges:
        params["badges"] = args.badges
    if args.fulfillment:
        params["fulfillment"] = args.fulfillment
    if args.include_brands:
        params["includeBrands"] = args.include_brands
    if args.exclude_brands:
        params["excludeBrands"] = args.exclude_brands

    params["sortBy"] = args.sort or "atLeastMonthlySales"
    params["sortOrder"] = args.order or "desc"
    params["pageSize"] = args.page_size or 20

    result = api_call("products/search", params)
    output(result, args.format)


def cmd_competitors(args):
    """Look up competitors by keyword, brand, ASIN, or category."""
    params = {}
    if args.keyword:
        params["keyword"] = args.keyword
    if args.brand:
        params["brand"] = args.brand
    if args.asin:
        params["asin"] = args.asin
    if args.category:
        params["categoryPath"] = parse_category(args.category)

    params["sortBy"] = args.sort or "atLeastMonthlySales"
    params["sortOrder"] = args.order or "desc"
    params["pageSize"] = args.page_size or 20

    result = api_call("products/competitor-lookup", params)
    output(result, args.format)


def cmd_product(args):
    """Get real-time product details for a single ASIN."""
    if not args.asin:
        print("ERROR: --asin is required for product command.", file=sys.stderr)
        sys.exit(1)
    params = {"asin": args.asin}
    if args.marketplace:
        params["marketplace"] = args.marketplace

    result = api_call("realtime/product", params)
    output(result, args.format)


def cmd_analyze(args):
    """Analyze reviews for ASINs or category with AI-powered insights."""
    params = {}

    # Determine mode from arguments
    if args.asin:
        params["asins"] = [args.asin]
        params["mode"] = "asin"
    elif args.asins:
        params["asins"] = [a.strip() for a in args.asins.split(",")]
        params["mode"] = "asin"
    elif args.category:
        params["categoryPath"] = parse_category(args.category)
        params["mode"] = "category"
    elif args.mode:
        params["mode"] = args.mode
    else:
        print("ERROR: --asin, --asins, or --category is required for analyze command.", file=sys.stderr)
        sys.exit(1)

    if args.label_type:
        params["labelType"] = args.label_type
    if args.period:
        params["period"] = args.period

    result = api_call("reviews/analyze", params)
    output(result, args.format)


def cmd_report(args):
    """
    Composite workflow: Full Market Report.
    Runs categories → markets/search → products/search → realtime/product (top 1).
    Outputs combined JSON with all results.
    """
    keyword = args.keyword
    if not keyword:
        print("ERROR: --keyword is required for report command.", file=sys.stderr)
        sys.exit(1)

    topn = str(args.topn or 10)
    results = {}

    # Step 1: Confirm category
    print("Step 1/4: Confirming category...", file=sys.stderr)
    cat_result = api_call("categories", {"categoryKeyword": keyword})
    results["categories"] = cat_result
    cat_data = cat_result.get("data", [])

    # Use the first matching category path
    category_path = None
    if cat_data:
        category_path = cat_data[0].get("categoryPath")

    # Step 2: Market data
    print("Step 2/4: Pulling market data...", file=sys.stderr)
    market_params = {"topN": topn}
    if category_path:
        market_params["categoryPath"] = category_path
    else:
        market_params["categoryKeyword"] = keyword
    market_result = api_call("markets/search", market_params)
    results["market"] = market_result

    # Step 3: Top products
    print("Step 3/4: Searching top products...", file=sys.stderr)
    products_result = api_call("products/search", {
        "keyword": keyword,
        "sortBy": "atLeastMonthlySales",
        "sortOrder": "desc",
        "pageSize": 50,
    })
    results["products"] = products_result

    # Step 4: Top 1 ASIN detail
    product_data = products_result.get("data", [])
    if product_data:
        top_asin = product_data[0].get("asin")
        if top_asin:
            print(f"Step 4/4: Getting details for top ASIN {top_asin}...", file=sys.stderr)
            detail_result = api_call("realtime/product", {"asin": top_asin, "marketplace": "US"})
            results["topProductDetail"] = detail_result
    else:
        print("Step 4/4: No products found, skipping detail.", file=sys.stderr)

    print("Done.", file=sys.stderr)
    output(results, args.format)


def cmd_opportunity(args):
    """
    Composite workflow: Product Opportunity Discovery.
    Runs categories → markets/search → products/search (filtered) → realtime/product (top 3).
    """
    keyword = args.keyword
    if not keyword:
        print("ERROR: --keyword is required for opportunity command.", file=sys.stderr)
        sys.exit(1)

    results = {}

    # Step 1: Confirm category
    print("Step 1/4: Confirming category...", file=sys.stderr)
    cat_result = api_call("categories", {"categoryKeyword": keyword})
    results["categories"] = cat_result
    cat_data = cat_result.get("data", [])
    category_path = cat_data[0].get("categoryPath") if cat_data else None

    # Step 2: Market validation
    print("Step 2/4: Validating market...", file=sys.stderr)
    market_params = {"topN": "10"}
    if category_path:
        market_params["categoryPath"] = category_path
    else:
        market_params["categoryKeyword"] = keyword
    results["market"] = api_call("markets/search", market_params)

    # Step 3: Product candidates (high demand, low barrier)
    print("Step 3/4: Discovering product candidates...", file=sys.stderr)
    search_params = {
        "keyword": keyword,
        "monthlySalesMin": 300,
        "reviewCountMax": 50,
        "sortBy": "atLeastMonthlySales",
        "sortOrder": "desc",
        "pageSize": 20,
    }
    # Apply mode override if specified
    if args.mode and args.mode in PRODUCT_MODES:
        search_params.update(PRODUCT_MODES[args.mode])
    results["products"] = api_call("products/search", search_params)

    # Step 4: Detail for top 3 ASINs
    product_data = results["products"].get("data", [])
    details = []
    for p in product_data[:3]:
        asin = p.get("asin")
        if asin:
            print(f"Step 4/4: Getting details for {asin}...", file=sys.stderr)
            details.append(api_call("realtime/product", {"asin": asin, "marketplace": "US"}))
    results["topProductDetails"] = details

    print("Done.", file=sys.stderr)
    output(results, args.format)


def cmd_check(args):
    """
    API self-check: verify API connectivity and available endpoints.
    Tests each endpoint with a simple query.
    """
    print("APIClaw API Self-Check\n", file=sys.stderr)
    print("=" * 50, file=sys.stderr)

    # Check API key from environment variable
    api_key = os.environ.get("APICLAW_API_KEY", "").strip()
    key_source = "env"

    # If not in env, check config file
    if not api_key:
        config_path = os.path.expanduser("~/.apiclaw/config.json")
        if os.path.exists(config_path):
            try:
                with open(config_path, "r", encoding="utf-8") as f:
                    config = json.load(f)
                    api_key = config.get("api_key", "").strip()
                    key_source = "config"
            except (json.JSONDecodeError, IOError):
                pass

    if api_key:
        source_label = "~/.apiclaw/config.json" if key_source == "config" else "environment variable"
        print(f"✅ API Key found (source: {source_label})", file=sys.stderr)
    else:
        print("❌ API Key: Not found", file=sys.stderr)
        print("   Checked: $APICLAW_API_KEY, ~/.apiclaw/config.json", file=sys.stderr)
        print("   Get one at: https://apiclaw.io/api-keys", file=sys.stderr)
        sys.exit(1)

    print(f"\nTesting endpoints on {BASE_URL}...\n", file=sys.stderr)

    endpoints = [
        ("categories", {}, "Category tree"),
        ("markets/search", {"categoryKeyword": "pet", "pageSize": 1}, "Market search"),
        ("products/search", {"keyword": "test", "pageSize": 1}, "Product search"),
        ("products/competitor-lookup", {"keyword": "test", "pageSize": 1}, "Competitor lookup"),
    ]

    results = {}
    all_ok = True

    for endpoint, params, desc in endpoints:
        try:
            result = api_call(endpoint, params)
            data_count = len(result.get("data", []))
            print(f"✅ {endpoint:30} OK (returned {data_count} items)", file=sys.stderr)
            results[endpoint] = {"status": "ok", "items": data_count}
        except SystemExit:
            print(f"❌ {endpoint:30} FAILED", file=sys.stderr)
            results[endpoint] = {"status": "failed"}
            all_ok = False
        except Exception as e:
            print(f"❌ {endpoint:30} ERROR: {e}", file=sys.stderr)
            results[endpoint] = {"status": "error", "message": str(e)}
            all_ok = False

    # Note: realtime/product and reviews/analyze require valid ASINs, skip in self-check
    print(f"⏭️  realtime/product            (skipped, requires valid ASIN)", file=sys.stderr)
    print(f"⏭️  reviews/analyze             (skipped, requires valid ASIN or category)", file=sys.stderr)

    print("\n" + "=" * 50, file=sys.stderr)
    if all_ok:
        print("✅ All endpoints operational", file=sys.stderr)
    else:
        print("⚠️  Some endpoints failed. Check API key or network.", file=sys.stderr)

    print(f"\nAPI Docs: {API_DOCS}", file=sys.stderr)

    output({"check": "complete", "endpoints": results}, args.format)


# ─── CLI Setup ───────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="APIClaw CLI — Amazon Product Research",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s categories --keyword "pet supplies"
  %(prog)s market --category "Pet Supplies,Dogs" --topn 10
  %(prog)s products --keyword "yoga mat" --mode beginner
  %(prog)s products --keyword "yoga mat" --sales-min 300 --reviews-max 50
  %(prog)s competitors --keyword "wireless earbuds" --brand Anker
  %(prog)s product --asin B09V3KXJPB
  %(prog)s report --keyword "pet supplies"
  %(prog)s opportunity --keyword "pet supplies" --mode high-demand-low-barrier
  %(prog)s check                                            # API self-check
        """,
    )

    # Common args
    parser.add_argument("--format", choices=["json", "compact"], default="json",
                        help="Output format (default: json)")

    sub = parser.add_subparsers(dest="command", required=True)

    # ── categories ──
    p_cat = sub.add_parser("categories", help="Query Amazon category tree")
    p_cat.add_argument("--keyword", help="Search categories by keyword")
    p_cat.add_argument("--category", help="Exact category path (comma-separated)")
    p_cat.add_argument("--parent", help="Get child categories (comma-separated parent path)")
    p_cat.set_defaults(func=cmd_categories)

    # ── market ──
    p_mkt = sub.add_parser("market", help="Search market-level data for a category")
    p_mkt.add_argument("--category", help="Category path (comma-separated)")
    p_mkt.add_argument("--keyword", help="Category keyword")
    p_mkt.add_argument("--topn", type=int, default=10, help="Top N for concentration analysis (default: 10)")
    p_mkt.add_argument("--page-size", type=int, default=20)
    p_mkt.add_argument("--sort", help="Sort field")
    p_mkt.add_argument("--order", choices=["asc", "desc"], default="desc")
    p_mkt.set_defaults(func=cmd_market)

    # ── products ──
    p_prod = sub.add_parser("products", help="Search products with filters (product selection)")
    p_prod.add_argument("--keyword", help="Search keyword")
    p_prod.add_argument("--category", help="Category path (comma-separated)")
    p_prod.add_argument("--mode", help=f"Preset filter mode: {', '.join(sorted(PRODUCT_MODES.keys()))}")
    p_prod.add_argument("--sales-min", type=int, help="Min monthly sales")
    p_prod.add_argument("--sales-max", type=int, help="Max monthly sales")
    p_prod.add_argument("--reviews-min", type=int, help="Min review count")
    p_prod.add_argument("--reviews-max", type=int, help="Max review count")
    p_prod.add_argument("--price-min", type=float, help="Min price")
    p_prod.add_argument("--price-max", type=float, help="Max price")
    p_prod.add_argument("--rating-min", type=float, help="Min rating")
    p_prod.add_argument("--rating-max", type=float, help="Max rating")
    p_prod.add_argument("--growth-min", type=float, help="Min sales growth rate")
    p_prod.add_argument("--bsr-min", type=int, help="Min BSR rank")
    p_prod.add_argument("--bsr-max", type=int, help="Max BSR rank")
    p_prod.add_argument("--seller-count-min", type=int, help="Min seller count")
    p_prod.add_argument("--seller-count-max", type=int, help="Max seller count")
    p_prod.add_argument("--variant-count-max", type=int, help="Max variant count")
    p_prod.add_argument("--keyword-match-type", choices=["fuzzy", "phrase", "exact"],
                        help="Keyword match type (default: fuzzy)")
    p_prod.add_argument("--sub-bsr-max", type=int, help="Max sub-category BSR rank")
    p_prod.add_argument("--exclude-keywords", help="Keywords to exclude (comma-separated)")
    p_prod.add_argument("--listing-age", help="Max listing age in days (string)")
    p_prod.add_argument("--badges", nargs="+", help="Badge filters (e.g. 'New Release')")
    p_prod.add_argument("--fulfillment", nargs="+", help="Fulfillment filter (FBA, FBM)")
    p_prod.add_argument("--include-brands", help="Include brands (comma-separated)")
    p_prod.add_argument("--exclude-brands", help="Exclude brands (comma-separated)")
    p_prod.add_argument("--page-size", type=int, default=20)
    p_prod.add_argument("--sort", help="Sort field (default: atLeastMonthlySales)")
    p_prod.add_argument("--order", choices=["asc", "desc"], default="desc")
    p_prod.set_defaults(func=cmd_products)

    # ── competitors ──
    p_comp = sub.add_parser("competitors", help="Look up competitors")
    p_comp.add_argument("--keyword", help="Search keyword")
    p_comp.add_argument("--brand", help="Brand filter")
    p_comp.add_argument("--asin", help="ASIN filter")
    p_comp.add_argument("--category", help="Category path (comma-separated)")
    p_comp.add_argument("--page-size", type=int, default=20)
    p_comp.add_argument("--sort", help="Sort field (default: atLeastMonthlySales)")
    p_comp.add_argument("--order", choices=["asc", "desc"], default="desc")
    p_comp.set_defaults(func=cmd_competitors)

    # ── product (single ASIN) ──
    p_single = sub.add_parser("product", help="Get real-time details for one ASIN")
    p_single.add_argument("--asin", required=True, help="ASIN (required)")
    p_single.add_argument("--marketplace", default="US",
                          help="Marketplace: US/UK/DE/FR/IT/ES/JP/CA/AU/IN/MX/BR (default: US)")
    p_single.set_defaults(func=cmd_product)

    # ── analyze (review analysis) ──
    p_analyze = sub.add_parser("analyze", help="Analyze reviews (sentiment, insights, pain points)")
    p_analyze.add_argument("--asin", help="Single ASIN to analyze")
    p_analyze.add_argument("--asins", help="Multiple ASINs (comma-separated, max 100)")
    p_analyze.add_argument("--category", help="Category path for category-level analysis")
    p_analyze.add_argument("--label-type",
                           help="Insight dimension filter: painPoints,issues,positives,improvements,"
                                "buyingFactors,scenarios,keywords,userProfiles,usageTimes,"
                                "usageLocations,behaviors")
    p_analyze.add_argument("--period", help="Time period (e.g. 90d)")
    p_analyze.add_argument("--mode", choices=["asin", "category"],
                           help="Query mode (auto-detected from --asin/--category)")
    p_analyze.set_defaults(func=cmd_analyze)

    # ── report (composite) ──
    p_report = sub.add_parser("report", help="Full market analysis report (composite workflow)")
    p_report.add_argument("--keyword", required=True, help="Category/niche keyword")
    p_report.add_argument("--topn", type=int, default=10, help="Top N (default: 10)")
    p_report.set_defaults(func=cmd_report)

    # ── opportunity (composite) ──
    p_opp = sub.add_parser("opportunity", help="Product opportunity discovery (composite workflow)")
    p_opp.add_argument("--keyword", required=True, help="Category/niche keyword")
    p_opp.add_argument("--mode", help="Product search mode preset")
    p_opp.set_defaults(func=cmd_opportunity)

    # ── check (API self-check) ──
    p_check = sub.add_parser("check", help="Fetch latest OpenAPI spec to verify available endpoints")
    p_check.set_defaults(func=cmd_check)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
