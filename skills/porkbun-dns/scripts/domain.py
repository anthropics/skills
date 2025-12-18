#!/usr/bin/env python3
"""
Porkbun Domain Management.

Usage:
    python domain.py list                       # List all domains
    python domain.py info example.com           # Domain details
    python domain.py ns example.com             # Get nameservers
"""

import argparse
import json
import os
import sys

CONFIG_FILE = os.path.expanduser("~/.config/porkbun-cli/config.json")

def load_config():
    """Load API credentials."""
    if os.path.exists(CONFIG_FILE):
        with open(CONFIG_FILE) as f:
            return json.load(f)
    return {
        "apikey": os.environ.get("PORKBUN_API_KEY"),
        "secretapikey": os.environ.get("PORKBUN_SECRET_KEY")
    }

def api_request(endpoint: str, data: dict = None) -> dict:
    """Make API request to Porkbun."""
    try:
        import requests
    except ImportError:
        return {"error": "requests library required: pip install requests"}

    config = load_config()
    if not config.get("apikey") or not config.get("secretapikey"):
        return {"error": "API credentials not configured. Run: python configure.py"}

    url = f"https://api.porkbun.com/api/json/v3/{endpoint}"
    payload = {
        "apikey": config["apikey"],
        "secretapikey": config["secretapikey"]
    }
    if data:
        payload.update(data)

    try:
        response = requests.post(url, json=payload)
        result = response.json()
        if result.get("status") == "ERROR":
            return {"error": result.get("message", "Unknown error")}
        return result
    except Exception as e:
        return {"error": str(e)}

def list_domains() -> dict:
    """List all domains in account."""
    return api_request("domain/listAll")

def get_nameservers(domain: str) -> dict:
    """Get nameservers for domain."""
    return api_request(f"domain/getNs/{domain}")

def update_nameservers(domain: str, nameservers: list) -> dict:
    """Update nameservers for domain."""
    return api_request(f"domain/updateNs/{domain}", {"ns": nameservers})

def format_domains(result: dict) -> str:
    """Format domain list."""
    if "error" in result:
        return f"Error: {result['error']}"

    domains = result.get("domains", [])
    if not domains:
        return "No domains found."

    lines = [
        f"{'Domain':<40} {'Expires':<15} {'Auto-Renew':<12} {'Status':<10}",
        "-" * 80
    ]
    for d in domains:
        lines.append(
            f"{d.get('domain', ''):<40} "
            f"{d.get('expireDate', '')[:10]:<15} "
            f"{'Yes' if d.get('autoRenew') else 'No':<12} "
            f"{d.get('status', ''):<10}"
        )

    return "\n".join(lines)

def main():
    parser = argparse.ArgumentParser(
        description="Porkbun Domain Management",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python domain.py list                         List all domains
  python domain.py ns example.com               Get nameservers
  python domain.py ns example.com --set ns1.custom.com ns2.custom.com
        """
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # List command
    list_parser = subparsers.add_parser("list", help="List domains")
    list_parser.add_argument("--json", action="store_true", help="JSON output")

    # Nameservers command
    ns_parser = subparsers.add_parser("ns", help="Nameserver management")
    ns_parser.add_argument("domain", help="Domain name")
    ns_parser.add_argument("--set", nargs="+", metavar="NS", help="Set nameservers")
    ns_parser.add_argument("--json", action="store_true", help="JSON output")

    # Ping command
    ping_parser = subparsers.add_parser("ping", help="Test API connection")

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        return

    if args.command == "list":
        result = list_domains()
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            print(format_domains(result))

    elif args.command == "ns":
        if args.set:
            result = update_nameservers(args.domain, args.set)
            if "error" in result:
                print(f"Error: {result['error']}")
                sys.exit(1)
            print(f"Nameservers updated for {args.domain}")
        else:
            result = get_nameservers(args.domain)
            if args.json:
                print(json.dumps(result, indent=2))
            elif "error" in result:
                print(f"Error: {result['error']}")
            else:
                print(f"Nameservers for {args.domain}:")
                for ns in result.get("ns", []):
                    print(f"  {ns}")

    elif args.command == "ping":
        result = api_request("ping")
        if "error" in result:
            print(f"Error: {result['error']}")
            sys.exit(1)
        print(f"API connection successful. Your IP: {result.get('yourIp', 'unknown')}")

if __name__ == "__main__":
    main()
