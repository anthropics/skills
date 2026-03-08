#!/usr/bin/env python3
"""OHAP Client — Open Hardware Agent Protocol client for Claude.

Usage:
    python ohap_client.py --host 192.168.1.100 --action info
    python ohap_client.py --host 192.168.1.100 --action read-all
    python ohap_client.py --host 192.168.1.100 --action read --sensor temp_1
    python ohap_client.py --host 192.168.1.100 --action command --cmd set_gpio --params '{"pin": 18, "state": "high"}'
    python ohap_client.py --host 192.168.1.100 --action health
    python ohap_client.py --discover
"""

import argparse
import json
import sys
import urllib.request
import urllib.error


def fetch(host: str, port: int, path: str, method: str = "GET",
          body: dict | None = None, token: str | None = None) -> dict:
    url = f"http://{host}:{port}{path}"
    data = json.dumps(body).encode() if body else None
    headers = {"Content-Type": "application/json"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            return json.loads(resp.read().decode())
    except urllib.error.HTTPError as e:
        return {"error": f"HTTP {e.code}", "detail": e.read().decode()}
    except urllib.error.URLError as e:
        return {"error": "Connection failed", "detail": str(e.reason)}
    except Exception as e:
        return {"error": "Unexpected error", "detail": str(e)}


def discover():
    """Discover OHAP devices on local network via mDNS."""
    try:
        from zeroconf import ServiceBrowser, Zeroconf, ServiceStateChange
        devices = []

        def on_change(zc, service_type, name, state_change):
            if state_change is ServiceStateChange.Added:
                info = zc.get_service_info(service_type, name)
                if info:
                    addr = ".".join(str(b) for b in info.addresses[0]) if info.addresses else "unknown"
                    devices.append({
                        "name": name,
                        "host": addr,
                        "port": info.port,
                    })

        zc = Zeroconf()
        ServiceBrowser(zc, "_ohap._tcp.local.", handlers=[on_change])
        import time
        time.sleep(3)
        zc.close()
        return {"devices": devices, "count": len(devices)}
    except ImportError:
        return {"error": "zeroconf not installed", "hint": "pip install zeroconf"}


def main():
    parser = argparse.ArgumentParser(description="OHAP Client — talk to hardware devices")
    parser.add_argument("--host", help="Device IP or hostname")
    parser.add_argument("--port", type=int, default=8421, help="Device port (default: 8421)")
    parser.add_argument("--token", help="Auth token")
    parser.add_argument("--action", choices=["info", "sensors", "read", "read-all", "command", "health", "discover"],
                        required=True)
    parser.add_argument("--sensor", help="Sensor ID for read action")
    parser.add_argument("--cmd", help="Command name for command action")
    parser.add_argument("--params", help="JSON params for command action")
    args = parser.parse_args()

    if args.action == "discover":
        result = discover()
        print(json.dumps(result, indent=2))
        return

    if not args.host:
        print(json.dumps({"error": "No host specified. Use --host or --action discover"}))
        sys.exit(1)

    if args.action == "info":
        result = fetch(args.host, args.port, "/agent/info", token=args.token)
    elif args.action == "sensors":
        result = fetch(args.host, args.port, "/agent/sensors", token=args.token)
    elif args.action == "read":
        sensor = args.sensor or "all"
        result = fetch(args.host, args.port, f"/agent/read/{sensor}", token=args.token)
    elif args.action == "read-all":
        result = fetch(args.host, args.port, "/agent/read/all", token=args.token)
    elif args.action == "command":
        if not args.cmd:
            print(json.dumps({"error": "No command specified. Use --cmd"}))
            sys.exit(1)
        params = json.loads(args.params) if args.params else {}
        body = {"command": args.cmd, "params": params}
        result = fetch(args.host, args.port, "/agent/command", method="POST",
                       body=body, token=args.token)
    elif args.action == "health":
        result = fetch(args.host, args.port, "/agent/health", token=args.token)
    else:
        result = {"error": f"Unknown action: {args.action}"}

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
