#!/usr/bin/env python3
"""
Port Management Script

Find available ports, check port usage, and manage port allocations.
"""

import argparse
import json
import socket
import subprocess
import sys

# Known port allocations
KNOWN_PORTS = {
    80: "caddy (http)",
    443: "caddy (https)",
    1131: "altproxy",
    1266: "clinical",
    3034: "coca",
    4108: "lessonplanner",
    5001: "swarm",
    5009: "beltalowda",
    5013: "etymology",
    5050: "skymarshal",
    5060: "mcp-orchestrator",
    5080: "dreamwalker",
    5211: "luke",
    5413: "studio",
    8000: "storyblocks",
    8847: "wordblocks",
    9999: "dashboard",
}

# Reserved ranges for testing
TEST_RANGES = [(5010, 5019), (5050, 5059)]


def is_port_available(port: int) -> bool:
    """Check if a port is available to bind."""
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(1)
        sock.bind(("127.0.0.1", port))
        sock.close()
        return True
    except OSError:
        return False


def get_port_process(port: int) -> dict:
    """Get process using a port."""
    try:
        result = subprocess.run(
            ["ss", "-tlnp", f"sport = :{port}"],
            capture_output=True,
            text=True,
            timeout=10,
        )

        lines = result.stdout.strip().split("\n")

        for line in lines[1:]:  # Skip header
            if f":{port}" in line:
                parts = line.split()
                process = parts[-1] if parts else "unknown"
                return {
                    "port": port,
                    "in_use": True,
                    "process": process,
                    "known_as": KNOWN_PORTS.get(port),
                }

        return {"port": port, "in_use": False, "known_as": KNOWN_PORTS.get(port)}

    except Exception as e:
        return {"port": port, "in_use": None, "error": str(e)}


def find_available_port(start: int = 5010, end: int = 5019) -> int:
    """Find first available port in range."""
    for port in range(start, end + 1):
        if is_port_available(port):
            return port
    return None


def list_used_ports(start: int = 1000, end: int = 9999) -> list:
    """List all ports in use within range."""
    try:
        result = subprocess.run(
            ["ss", "-tlnp"], capture_output=True, text=True, timeout=10
        )

        used = []

        for line in result.stdout.split("\n"):
            if "LISTEN" in line:
                # Extract port from address
                parts = line.split()
                for part in parts:
                    if ":" in part:
                        try:
                            addr = part.rsplit(":", 1)
                            port = int(addr[-1])
                            if start <= port <= end:
                                used.append(
                                    {"port": port, "known_as": KNOWN_PORTS.get(port)}
                                )
                        except (ValueError, IndexError):
                            continue

        # Deduplicate and sort
        seen = set()
        unique = []
        for p in sorted(used, key=lambda x: x["port"]):
            if p["port"] not in seen:
                seen.add(p["port"])
                unique.append(p)

        return unique

    except Exception as e:
        return [{"error": str(e)}]


def get_port_map() -> dict:
    """Get full port allocation map."""
    used_ports = list_used_ports()
    used_set = {p["port"] for p in used_ports if "port" in p}

    # Build map
    port_map = {
        "known_services": KNOWN_PORTS,
        "in_use": used_ports,
        "test_ranges": [
            {
                "range": f"{start}-{end}",
                "available": [p for p in range(start, end + 1) if p not in used_set],
            }
            for start, end in TEST_RANGES
        ],
    }

    return port_map


def format_output(data: dict | list, format_type: str = "text") -> str:
    """Format output."""
    if format_type == "json":
        return json.dumps(data, indent=2)

    if isinstance(data, list):
        lines = []
        for item in data:
            if "error" in item:
                lines.append(f"Error: {item['error']}")
            else:
                port = item.get("port", "?")
                known = item.get("known_as", "")
                known_str = f" ({known})" if known else ""
                lines.append(f"  {port}{known_str}")
        return "\n".join(lines)

    elif isinstance(data, dict):
        if "port" in data:
            # Single port check
            port = data["port"]
            if data.get("error"):
                return f"Port {port}: Error - {data['error']}"
            elif data.get("in_use"):
                process = data.get("process", "unknown")
                return f"Port {port}: IN USE by {process}"
            else:
                return f"Port {port}: AVAILABLE"

        elif "known_services" in data:
            # Port map
            lines = [
                "=" * 50,
                "PORT ALLOCATION MAP",
                "=" * 50,
                "",
                "Known Services:",
                "-" * 30,
            ]

            for port, name in sorted(data["known_services"].items()):
                lines.append(f"  {port}: {name}")

            lines.append("")
            lines.append("Currently In Use:")
            lines.append("-" * 30)

            for item in data.get("in_use", []):
                port = item.get("port", "?")
                known = item.get("known_as", "")
                known_str = f" ({known})" if known else ""
                lines.append(f"  {port}{known_str}")

            lines.append("")
            lines.append("Test Ranges Available:")
            lines.append("-" * 30)

            for range_info in data.get("test_ranges", []):
                lines.append(f"  {range_info['range']}: {range_info['available']}")

            return "\n".join(lines)

        else:
            return json.dumps(data, indent=2)

    return str(data)


def main():
    parser = argparse.ArgumentParser(description="Port management utilities")

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # Find available port
    find_parser = subparsers.add_parser("find", help="Find available port")
    find_parser.add_argument(
        "--range", "-r", default="5010-5019", help="Port range (default: 5010-5019)"
    )

    # Check specific port
    check_parser = subparsers.add_parser("check", help="Check if port is available")
    check_parser.add_argument("port", type=int, help="Port to check")

    # List used ports
    list_parser = subparsers.add_parser("list", help="List ports")
    list_parser.add_argument(
        "--used", "-u", action="store_true", help="Show used ports"
    )
    list_parser.add_argument(
        "--range", "-r", default="1000-9999", help="Port range (default: 1000-9999)"
    )

    # Show port process
    process_parser = subparsers.add_parser("process", help="Show process using port")
    process_parser.add_argument("port", type=int, help="Port to check")

    # Port map
    subparsers.add_parser("map", help="Show full port allocation map")

    # Common options
    parser.add_argument(
        "--format",
        "-f",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )

    args = parser.parse_args()

    if not args.command:
        # Default to map
        args.command = "map"

    if args.command == "find":
        parts = args.range.split("-")
        start, end = int(parts[0]), int(parts[1])
        port = find_available_port(start, end)

        if port:
            print(f"Port {port} is available")
        else:
            print(f"No available ports in range {start}-{end}")
            sys.exit(1)

    elif args.command == "check":
        result = get_port_process(args.port)
        print(format_output(result, args.format))

        if result.get("in_use"):
            sys.exit(1)

    elif args.command == "list":
        parts = args.range.split("-")
        start, end = int(parts[0]), int(parts[1])

        if args.used:
            result = list_used_ports(start, end)
            print("Ports in use:")
            print(format_output(result, args.format))
        else:
            result = list_used_ports(start, end)
            print(format_output(result, args.format))

    elif args.command == "process":
        result = get_port_process(args.port)
        print(format_output(result, args.format))

    elif args.command == "map":
        result = get_port_map()
        print(format_output(result, args.format))


if __name__ == "__main__":
    main()
