#!/usr/bin/env python3
"""
Porkbun DNS Record Management.

Usage:
    python dns.py list example.com              # List all records
    python dns.py create example.com A 1.2.3.4  # Create A record
    python dns.py delete example.com RECORD_ID  # Delete record
"""

import argparse
import json
import os
import sys

CONFIG_FILE = os.path.expanduser("~/.config/porkbun-cli/config.json")

DNS_TYPES = ["A", "AAAA", "CNAME", "ALIAS", "MX", "TXT", "NS", "SRV", "TLSA", "CAA", "HTTPS", "SVCB", "SSHFP"]

def load_config():
    """Load API credentials."""
    if os.path.exists(CONFIG_FILE):
        with open(CONFIG_FILE) as f:
            return json.load(f)
    # Check environment
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

def list_records(domain: str, record_type: str = None) -> dict:
    """List DNS records for domain."""
    if record_type:
        result = api_request(f"dns/retrieveByNameType/{domain}/{record_type}")
    else:
        result = api_request(f"dns/retrieve/{domain}")
    return result

def create_record(domain: str, record_type: str, content: str,
                  name: str = None, prio: int = None, ttl: int = None) -> dict:
    """Create DNS record."""
    data = {"type": record_type.upper(), "content": content}
    if name:
        data["name"] = name
    if prio is not None:
        data["prio"] = str(prio)
    if ttl is not None:
        data["ttl"] = str(ttl)
    return api_request(f"dns/create/{domain}", data)

def edit_record(domain: str, record_id: str, record_type: str, content: str,
                name: str = None, prio: int = None, ttl: int = None) -> dict:
    """Edit DNS record."""
    data = {"type": record_type.upper(), "content": content}
    if name:
        data["name"] = name
    if prio is not None:
        data["prio"] = str(prio)
    if ttl is not None:
        data["ttl"] = str(ttl)
    return api_request(f"dns/edit/{domain}/{record_id}", data)

def delete_record(domain: str, record_id: str) -> dict:
    """Delete DNS record."""
    return api_request(f"dns/delete/{domain}/{record_id}")

def format_records(result: dict) -> str:
    """Format records for display."""
    if "error" in result:
        return f"Error: {result['error']}"

    records = result.get("records", [])
    if not records:
        return "No records found."

    lines = [
        f"{'ID':<12} {'Type':<8} {'Name':<30} {'Content':<40} {'TTL':<8}",
        "-" * 100
    ]
    for r in records:
        name = r.get("name", "") or "(root)"
        content = r.get("content", "")[:38]
        lines.append(f"{r.get('id', ''):<12} {r.get('type', ''):<8} {name:<30} {content:<40} {r.get('ttl', ''):<8}")

    return "\n".join(lines)

def main():
    parser = argparse.ArgumentParser(
        description="Porkbun DNS Record Management",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python dns.py list example.com                  List all records
  python dns.py list example.com --type A         List only A records
  python dns.py create example.com A 1.2.3.4      Create A record (root)
  python dns.py create example.com A 1.2.3.4 -n www  Create A for subdomain
  python dns.py create example.com MX mail.ex.com -p 10  MX with priority
  python dns.py edit example.com ID A 5.6.7.8     Edit record
  python dns.py delete example.com ID             Delete record
        """
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # List command
    list_parser = subparsers.add_parser("list", help="List DNS records")
    list_parser.add_argument("domain", help="Domain name")
    list_parser.add_argument("--type", "-t", choices=DNS_TYPES, help="Filter by type")
    list_parser.add_argument("--json", action="store_true", help="JSON output")

    # Create command
    create_parser = subparsers.add_parser("create", help="Create DNS record")
    create_parser.add_argument("domain", help="Domain name")
    create_parser.add_argument("type", choices=DNS_TYPES, help="Record type")
    create_parser.add_argument("content", help="Record content")
    create_parser.add_argument("--name", "-n", help="Subdomain name")
    create_parser.add_argument("--prio", "-p", type=int, help="Priority (MX, SRV)")
    create_parser.add_argument("--ttl", type=int, help="TTL in seconds")

    # Edit command
    edit_parser = subparsers.add_parser("edit", help="Edit DNS record")
    edit_parser.add_argument("domain", help="Domain name")
    edit_parser.add_argument("id", help="Record ID")
    edit_parser.add_argument("type", choices=DNS_TYPES, help="Record type")
    edit_parser.add_argument("content", help="New content")
    edit_parser.add_argument("--name", "-n", help="Subdomain name")
    edit_parser.add_argument("--prio", "-p", type=int, help="Priority")
    edit_parser.add_argument("--ttl", type=int, help="TTL")

    # Delete command
    delete_parser = subparsers.add_parser("delete", help="Delete DNS record")
    delete_parser.add_argument("domain", help="Domain name")
    delete_parser.add_argument("id", help="Record ID")
    delete_parser.add_argument("--yes", "-y", action="store_true", help="Skip confirmation")

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        return

    if args.command == "list":
        result = list_records(args.domain, args.type)
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            print(format_records(result))

    elif args.command == "create":
        result = create_record(args.domain, args.type, args.content,
                               args.name, args.prio, args.ttl)
        if "error" in result:
            print(f"Error: {result['error']}")
            sys.exit(1)
        print("Record created successfully.")

    elif args.command == "edit":
        result = edit_record(args.domain, args.id, args.type, args.content,
                            args.name, args.prio, args.ttl)
        if "error" in result:
            print(f"Error: {result['error']}")
            sys.exit(1)
        print("Record updated successfully.")

    elif args.command == "delete":
        if not args.yes:
            confirm = input(f"Delete record {args.id} from {args.domain}? [y/N] ")
            if confirm.lower() != "y":
                print("Cancelled.")
                return
        result = delete_record(args.domain, args.id)
        if "error" in result:
            print(f"Error: {result['error']}")
            sys.exit(1)
        print("Record deleted successfully.")

if __name__ == "__main__":
    main()
