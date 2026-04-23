#!/usr/bin/env python3
"""
和风天气查询脚本
使用和风天气 API (QWeather) 获取中国任意城市/地区的天气信息

用法: python get_weather.py <城市名称> [--type now|3d|7d|all]

首次使用前，请先配置 API Key（免费注册：https://dev.qweather.com）：
    python get_weather.py --setup
"""

import sys
import json
import os
import argparse
import urllib.request
import urllib.parse
import urllib.error
from pathlib import Path
from datetime import datetime

# ===== API Key 配置管理 =====
CONFIG_DIR = Path.home() / ".config" / "weather-query"
CONFIG_FILE = CONFIG_DIR / "config.json"

GEO_BASE_URL = "https://geoapi.qweather.com/v2/city/lookup"
WEATHER_BASE_URL = "https://devapi.qweather.com/v7/weather"
AIR_BASE_URL = "https://devapi.qweather.com/v7/air/now"


def get_api_key():
    """
    按优先级获取 API Key：
    1. 环境变量 QWEATHER_API_KEY
    2. 配置文件 ~/.config/weather-query/config.json
    3. 如果都没有，提示用户配置
    """
    # 1. 优先读取环境变量
    key = os.environ.get("QWEATHER_API_KEY", "").strip()
    if key:
        return key

    # 2. 读取配置文件
    if CONFIG_FILE.exists():
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                config = json.load(f)
                key = config.get("api_key", "").strip()
                if key:
                    return key
        except (json.JSONDecodeError, IOError):
            pass

    # 3. 未找到 Key，给出友好提示
    print("❌ 未找到和风天气 API Key！", file=sys.stderr)
    print("", file=sys.stderr)
    print("📝 请按照以下步骤配置：", file=sys.stderr)
    print("   1. 前往 https://dev.qweather.com 免费注册账号", file=sys.stderr)
    print("   2. 创建应用并获取 API Key", file=sys.stderr)
    print("   3. 运行以下命令保存 Key（只需配置一次）：", file=sys.stderr)
    print("      python get_weather.py --setup", file=sys.stderr)
    print("", file=sys.stderr)
    print("💡 或者设置环境变量（临时使用）：", file=sys.stderr)
    print("      export QWEATHER_API_KEY=你的ApiKey", file=sys.stderr)
    sys.exit(1)


def setup_api_key():
    """交互式配置并保存 API Key"""
    print("🔧 和风天气 API Key 配置向导")
    print("─" * 40)
    print("1. 请前往 https://dev.qweather.com 注册（免费）")
    print("2. 登录后创建一个应用，获取 API Key")
    print("─" * 40)
    key = input("请粘贴你的 API Key：").strip()

    if not key:
        print("❌ API Key 不能为空")
        sys.exit(1)

    # 验证 Key 是否有效
    print("🔍 正在验证 API Key...")
    test_url = f"{GEO_BASE_URL}?location=%E5%8C%97%E4%BA%AC&key={key}"
    try:
        req = urllib.request.Request(test_url)
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode("utf-8"))
            if data.get("code") == "200":
                print("✅ API Key 验证成功！")
            elif data.get("code") == "401":
                print("❌ API Key 无效，请检查后重试")
                sys.exit(1)
            else:
                print(f"⚠️  API 返回码: {data.get('code')}，Key 可能有问题，仍继续保存")
    except Exception as e:
        print(f"⚠️  网络验证失败（{e}），仍继续保存")

    # 保存到配置文件
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump({"api_key": key}, f, ensure_ascii=False, indent=2)

    print(f"✅ API Key 已保存到：{CONFIG_FILE}")
    print("🌤️  现在你可以查询天气了，例如：")
    print("      python get_weather.py 北京")


def fetch_json(url):
    """发起 GET 请求并返回 JSON 数据"""
    try:
        req = urllib.request.Request(url, headers={"Accept-Encoding": "gzip, deflate"})
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = resp.read()
            if resp.info().get("Content-Encoding") == "gzip":
                import gzip
                data = gzip.decompress(data)
            return json.loads(data.decode("utf-8"))
    except urllib.error.HTTPError as e:
        print(f"❌ HTTP 错误: {e.code} - {e.reason}", file=sys.stderr)
        sys.exit(1)
    except urllib.error.URLError as e:
        print(f"❌ 网络连接错误: {e.reason}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError:
        print("❌ 解析 API 响应失败，返回数据格式异常", file=sys.stderr)
        sys.exit(1)


def lookup_city(city_name, api_key):
    """根据城市名称查询城市信息，返回 location_id 和城市详情"""
    encoded = urllib.parse.quote(city_name)
    url = f"{GEO_BASE_URL}?location={encoded}&key={api_key}&lang=zh&number=5"
    data = fetch_json(url)

    if data.get("code") != "200":
        code = data.get("code", "未知")
        if code == "404":
            print(f"❌ 未找到城市「{city_name}」，请检查城市名称是否正确", file=sys.stderr)
        elif code == "401":
            print("❌ API Key 无效或已过期，请运行 --setup 重新配置", file=sys.stderr)
        else:
            print(f"❌ 城市查询失败，错误码: {code}", file=sys.stderr)
        sys.exit(1)

    locations = data.get("location", [])
    if not locations:
        print(f"❌ 未找到城市「{city_name}」，请尝试更精确的名称", file=sys.stderr)
        sys.exit(1)

    loc = locations[0]
    return {
        "id": loc["id"],
        "name": loc["name"],
        "adm1": loc.get("adm1", ""),
        "adm2": loc.get("adm2", ""),
        "country": loc.get("country", ""),
        "lat": loc.get("lat", ""),
        "lon": loc.get("lon", ""),
    }


def get_weather_now(location_id, api_key):
    """获取实时天气"""
    url = f"{WEATHER_BASE_URL}/now?location={location_id}&key={api_key}&lang=zh"
    data = fetch_json(url)
    if data.get("code") != "200":
        print(f"❌ 实时天气获取失败，错误码: {data.get('code')}", file=sys.stderr)
        return None
    return data.get("now", {})


def get_weather_daily(location_id, api_key, days=3):
    """获取未来 N 天天气预报"""
    url = f"{WEATHER_BASE_URL}/{days}d?location={location_id}&key={api_key}&lang=zh"
    data = fetch_json(url)
    if data.get("code") != "200":
        print(f"❌ 天气预报获取失败，错误码: {data.get('code')}", file=sys.stderr)
        return []
    return data.get("daily", [])


def get_air_quality(location_id, api_key):
    """获取实时空气质量"""
    url = f"{AIR_BASE_URL}?location={location_id}&key={api_key}&lang=zh"
    data = fetch_json(url)
    if data.get("code") != "200":
        return None
    return data.get("now", {})


def format_now(city_info, now, air=None):
    """格式化实时天气输出"""
    parts = []
    if city_info["country"] and city_info["country"] != "中国":
        parts.append(city_info["country"])
    if city_info["adm1"] and city_info["adm1"] != city_info["name"]:
        parts.append(city_info["adm1"])
    if city_info["adm2"] and city_info["adm2"] != city_info["name"]:
        parts.append(city_info["adm2"])
    parts.append(city_info["name"])
    city_display = " · ".join(parts)

    obs_time = now.get("obsTime", "")
    if obs_time:
        try:
            dt = datetime.fromisoformat(obs_time.replace("+08:00", ""))
            obs_time = dt.strftime("%Y年%m月%d日 %H:%M")
        except Exception:
            pass

    lines = []
    lines.append(f"🌍 {city_display} 实时天气")
    lines.append(f"📅 观测时间：{obs_time}")
    lines.append("─" * 36)
    lines.append(f"🌡️  温度：{now.get('temp', '--')}°C  （体感 {now.get('feelsLike', '--')}°C）")
    lines.append(f"☁️  天气：{now.get('text', '--')}")
    lines.append(f"💨 风向：{now.get('windDir', '--')}  {now.get('windScale', '--')}级  ({now.get('windSpeed', '--')} km/h)")
    lines.append(f"💧 湿度：{now.get('humidity', '--')}%")
    lines.append(f"🌧️  降水量：{now.get('precip', '--')} mm")
    lines.append(f"👁️  能见度：{now.get('vis', '--')} km")
    lines.append(f"🔽 气压：{now.get('pressure', '--')} hPa")

    if air:
        aqi = air.get("aqi", "--")
        category = air.get("category", "--")
        lines.append(f"🌿 空气质量：{category}（AQI {aqi}）")
        primary = air.get("primary", "")
        if primary and primary != "NA":
            lines.append(f"   主要污染物：{primary}")

    lines.append("─" * 36)
    return "\n".join(lines)


def format_daily(city_info, daily_list):
    """格式化多日预报输出"""
    if not daily_list:
        return ""

    lines = []
    lines.append(f"\n📆 未来 {len(daily_list)} 天天气预报")
    lines.append("─" * 36)

    for day in daily_list:
        date_str = day.get("fxDate", "")
        try:
            dt = datetime.strptime(date_str, "%Y-%m-%d")
            weekdays = ["周一", "周二", "周三", "周四", "周五", "周六", "周日"]
            weekday = weekdays[dt.weekday()]
            date_display = f"{dt.month}月{dt.day}日 {weekday}"
        except Exception:
            date_display = date_str

        temp_min = day.get("tempMin", "--")
        temp_max = day.get("tempMax", "--")
        text_day = day.get("textDay", "--")
        text_night = day.get("textNight", "--")
        wind_dir = day.get("windDirDay", "--")
        wind_scale = day.get("windScaleDay", "--")
        humidity = day.get("humidity", "--")
        precip = day.get("precip", "--")
        uv_index = day.get("uvIndex", "")

        weather_text = text_day if text_day == text_night else f"{text_day}转{text_night}"

        line = f"📅 {date_display}：{weather_text}"
        line += f"\n   🌡️  {temp_min}°C ~ {temp_max}°C  |  {wind_dir} {wind_scale}级"
        line += f"\n   💧 湿度 {humidity}%  |  🌧️  降水 {precip}mm"
        if uv_index:
            line += f"  |  ☀️  紫外线 {uv_index}"
        lines.append(line)
        lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="和风天气查询工具",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
使用示例:
  python get_weather.py --setup          # 首次配置 API Key
  python get_weather.py 北京             # 查询北京完整天气
  python get_weather.py 上海 --type now  # 只看实时天气
  python get_weather.py 成都 --type 7d   # 未来7天预报
        """
    )
    parser.add_argument("city", nargs="?", help="城市名称，如：北京、上海、成都")
    parser.add_argument("--setup", action="store_true", help="配置 API Key（首次使用必须运行）")
    parser.add_argument(
        "--type",
        choices=["now", "3d", "7d", "all"],
        default="all",
        help="查询类型：now=实时, 3d=3天预报, 7d=7天预报, all=全部（默认）"
    )
    parser.add_argument("--no-air", action="store_true", help="不查询空气质量")
    args = parser.parse_args()

    # 配置模式
    if args.setup:
        setup_api_key()
        return

    # 检查城市参数
    if not args.city:
        parser.print_help()
        sys.exit(1)

    city_name = args.city
    query_type = args.type

    # 获取 API Key
    api_key = get_api_key()

    print(f"🔍 正在查询「{city_name}」的天气信息...\n")

    # 查询城市
    city_info = lookup_city(city_name, api_key)
    location_id = city_info["id"]

    result_parts = []

    # 实时天气
    if query_type in ("now", "all"):
        now = get_weather_now(location_id, api_key)
        air = None
        if not args.no_air:
            air = get_air_quality(location_id, api_key)
        if now:
            result_parts.append(format_now(city_info, now, air))

    # 天气预报
    if query_type == "3d" or query_type == "all":
        daily = get_weather_daily(location_id, api_key, 3)
        if daily:
            result_parts.append(format_daily(city_info, daily))
    elif query_type == "7d":
        daily = get_weather_daily(location_id, api_key, 7)
        if daily:
            result_parts.append(format_daily(city_info, daily))

    print("\n".join(result_parts))
    print("\n💡 数据来源：和风天气 (QWeather.com)")


if __name__ == "__main__":
    main()
