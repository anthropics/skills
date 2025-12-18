#!/usr/bin/env python3
"""
Service Management Script

Manage services via the service manager (sm) CLI.
Supports status, start, stop, restart, and logs operations.
"""

import argparse
import json
import subprocess
import sys

SM_PATH = "/home/coolhand/service_manager.py"


def run_sm(command: str, service: str = None, extra_args: list = None) -> dict:
    """Run a service manager command."""
    cmd = ["python3", SM_PATH, command]

    if service:
        cmd.append(service)

    if extra_args:
        cmd.extend(extra_args)

    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)

        return {
            "success": result.returncode == 0,
            "output": result.stdout,
            "errors": result.stderr,
            "exit_code": result.returncode,
        }

    except FileNotFoundError:
        return {
            "success": False,
            "output": "",
            "errors": f"Service manager not found at {SM_PATH}",
            "exit_code": 1,
        }
    except subprocess.TimeoutExpired:
        return {
            "success": False,
            "output": "",
            "errors": "Command timed out",
            "exit_code": 1,
        }


def get_status(service: str = None, json_output: bool = False) -> dict:
    """Get status of service(s)."""
    extra = ["--json"] if json_output else []
    return run_sm("status", service, extra)


def start_service(service: str) -> dict:
    """Start a service."""
    return run_sm("start", service)


def stop_service(service: str) -> dict:
    """Stop a service."""
    return run_sm("stop", service)


def restart_service(service: str) -> dict:
    """Restart a service."""
    return run_sm("restart", service)


def get_logs(service: str, lines: int = 50, follow: bool = False) -> dict:
    """Get service logs."""
    extra = ["-n", str(lines)]
    if follow:
        extra.append("-f")
    return run_sm("logs", service, extra)


def format_status(result: dict, format_type: str = "text") -> str:
    """Format status output."""
    if format_type == "json":
        return json.dumps(
            {
                "success": result["success"],
                "output": result["output"],
                "errors": result["errors"] if result["errors"] else None,
            },
            indent=2,
        )

    if result["success"]:
        return result["output"]
    else:
        return f"Error: {result['errors']}\n{result['output']}"


def main():
    parser = argparse.ArgumentParser(description="Manage services via service manager")

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # Status command
    status_parser = subparsers.add_parser("status", help="Show service status")
    status_parser.add_argument(
        "service", nargs="?", help="Service name (all if omitted)"
    )
    status_parser.add_argument("--json", "-j", action="store_true", help="JSON output")

    # Start command
    start_parser = subparsers.add_parser("start", help="Start a service")
    start_parser.add_argument("service", help="Service name")
    start_parser.add_argument(
        "--all", "-a", action="store_true", help="Start all services"
    )

    # Stop command
    stop_parser = subparsers.add_parser("stop", help="Stop a service")
    stop_parser.add_argument("service", help="Service name")
    stop_parser.add_argument(
        "--all", "-a", action="store_true", help="Stop all services"
    )

    # Restart command
    restart_parser = subparsers.add_parser("restart", help="Restart a service")
    restart_parser.add_argument("service", help="Service name")

    # Logs command
    logs_parser = subparsers.add_parser("logs", help="View service logs")
    logs_parser.add_argument("service", help="Service name")
    logs_parser.add_argument(
        "--lines", "-n", type=int, default=50, help="Number of lines"
    )
    logs_parser.add_argument(
        "--follow", "-f", action="store_true", help="Follow log output"
    )

    # Info command
    info_parser = subparsers.add_parser("info", help="Show service info")
    info_parser.add_argument("service", help="Service name")

    # List command
    subparsers.add_parser("list", help="List all registered services")

    args = parser.parse_args()

    if not args.command:
        # Default to status
        result = get_status()
        print(format_status(result))
        return

    if args.command == "status":
        result = get_status(args.service, args.json)
        print(format_status(result, "json" if args.json else "text"))

    elif args.command == "start":
        if args.all:
            result = run_sm("start", "--all")
        else:
            result = start_service(args.service)
        print(format_status(result))
        if not result["success"]:
            sys.exit(1)

    elif args.command == "stop":
        if args.all:
            result = run_sm("stop", "--all")
        else:
            result = stop_service(args.service)
        print(format_status(result))
        if not result["success"]:
            sys.exit(1)

    elif args.command == "restart":
        result = restart_service(args.service)
        print(format_status(result))
        if not result["success"]:
            sys.exit(1)

    elif args.command == "logs":
        if args.follow:
            # For follow mode, run interactively
            subprocess.run(["python3", SM_PATH, "logs", args.service, "-f"])
        else:
            result = get_logs(args.service, args.lines)
            print(result["output"])

    elif args.command == "info":
        result = run_sm("info", args.service)
        print(format_status(result))

    elif args.command == "list":
        result = run_sm("list")
        print(format_status(result))


if __name__ == "__main__":
    main()
