#!/usr/bin/env python3
"""
System Health Check Script

Check health of system resources, services, and Caddy routes.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path


def check_cpu() -> dict:
    """Check CPU usage."""
    try:
        result = subprocess.run(
            ["top", "-bn1"], capture_output=True, text=True, timeout=10
        )

        # Parse CPU line
        for line in result.stdout.split("\n"):
            if "Cpu(s)" in line or "%Cpu" in line:
                parts = line.split()
                for i, part in enumerate(parts):
                    if "id" in part or part == "id,":
                        idle = float(parts[i - 1].replace(",", ""))
                        usage = 100 - idle
                        return {
                            "status": "ok"
                            if usage < 80
                            else "warning"
                            if usage < 95
                            else "critical",
                            "usage_pct": round(usage, 1),
                            "idle_pct": round(idle, 1),
                        }

        return {"status": "unknown", "error": "Could not parse CPU info"}

    except Exception as e:
        return {"status": "error", "error": str(e)}


def check_memory() -> dict:
    """Check memory usage."""
    try:
        result = subprocess.run(
            ["free", "-m"], capture_output=True, text=True, timeout=10
        )

        lines = result.stdout.strip().split("\n")
        mem_line = lines[1].split()

        total = int(mem_line[1])
        used = int(mem_line[2])
        available = int(mem_line[6]) if len(mem_line) > 6 else total - used

        usage_pct = (used / total) * 100

        return {
            "status": "ok"
            if usage_pct < 80
            else "warning"
            if usage_pct < 95
            else "critical",
            "total_mb": total,
            "used_mb": used,
            "available_mb": available,
            "usage_pct": round(usage_pct, 1),
        }

    except Exception as e:
        return {"status": "error", "error": str(e)}


def check_disk(path: str = "/") -> dict:
    """Check disk usage."""
    try:
        result = subprocess.run(
            ["df", "-h", path], capture_output=True, text=True, timeout=10
        )

        lines = result.stdout.strip().split("\n")
        disk_line = lines[1].split()

        total = disk_line[1]
        used = disk_line[2]
        available = disk_line[3]
        usage_pct = int(disk_line[4].replace("%", ""))

        return {
            "status": "ok"
            if usage_pct < 80
            else "warning"
            if usage_pct < 95
            else "critical",
            "path": path,
            "total": total,
            "used": used,
            "available": available,
            "usage_pct": usage_pct,
        }

    except Exception as e:
        return {"status": "error", "error": str(e)}


def check_services() -> dict:
    """Check service manager services."""
    try:
        result = subprocess.run(
            ["python3", "/home/coolhand/service_manager.py", "status"],
            capture_output=True,
            text=True,
            timeout=30,
        )

        lines = result.stdout.strip().split("\n")

        services = {"running": [], "stopped": [], "error": []}

        for line in lines:
            if "RUNNING" in line.upper():
                # Extract service name
                parts = line.split()
                if parts:
                    services["running"].append(parts[0])
            elif "STOPPED" in line.upper() or "NOT RUNNING" in line.upper():
                parts = line.split()
                if parts:
                    services["stopped"].append(parts[0])
            elif "ERROR" in line.upper() or "FAILED" in line.upper():
                parts = line.split()
                if parts:
                    services["error"].append(parts[0])

        total = (
            len(services["running"]) + len(services["stopped"]) + len(services["error"])
        )

        status = "ok"
        if services["error"]:
            status = "critical"
        elif len(services["stopped"]) > len(services["running"]):
            status = "warning"

        return {
            "status": status,
            "running": len(services["running"]),
            "stopped": len(services["stopped"]),
            "error": len(services["error"]),
            "total": total,
            "details": services,
        }

    except Exception as e:
        return {"status": "error", "error": str(e)}


def check_caddy() -> dict:
    """Check Caddy status."""
    try:
        # Check if Caddy is running
        result = subprocess.run(
            ["systemctl", "is-active", "caddy"],
            capture_output=True,
            text=True,
            timeout=10,
        )

        is_running = result.stdout.strip() == "active"

        # Validate config
        validate_result = subprocess.run(
            ["sudo", "-S", "caddy", "validate", "--config", "/etc/caddy/Caddyfile"],
            input="G@nym3de\n",
            capture_output=True,
            text=True,
            timeout=30,
        )

        config_valid = validate_result.returncode == 0

        return {
            "status": "ok"
            if is_running and config_valid
            else "warning"
            if is_running
            else "critical",
            "running": is_running,
            "config_valid": config_valid,
            "config_error": validate_result.stderr if not config_valid else None,
        }

    except Exception as e:
        return {"status": "error", "error": str(e)}


def check_ports(ports: list = None) -> dict:
    """Check if key ports are listening."""
    default_ports = [80, 443, 5060, 8000, 9999]
    ports = ports or default_ports

    try:
        result = subprocess.run(
            ["ss", "-tlnp"], capture_output=True, text=True, timeout=10
        )

        listening = []
        for line in result.stdout.split("\n"):
            for port in ports:
                if f":{port}" in line and "LISTEN" in line:
                    listening.append(port)

        listening = list(set(listening))
        not_listening = [p for p in ports if p not in listening]

        return {
            "status": "ok" if not not_listening else "warning",
            "listening": listening,
            "not_listening": not_listening,
            "checked": ports,
        }

    except Exception as e:
        return {"status": "error", "error": str(e)}


def run_health_check(
    include_cpu: bool = True,
    include_memory: bool = True,
    include_disk: bool = True,
    include_services: bool = True,
    include_caddy: bool = True,
    include_ports: bool = True,
    verbose: bool = False,
) -> dict:
    """Run comprehensive health check."""

    results = {"overall_status": "ok", "checks": {}}

    statuses = []

    if include_cpu:
        results["checks"]["cpu"] = check_cpu()
        statuses.append(results["checks"]["cpu"]["status"])
        if verbose:
            print("[INFO] CPU check complete")

    if include_memory:
        results["checks"]["memory"] = check_memory()
        statuses.append(results["checks"]["memory"]["status"])
        if verbose:
            print("[INFO] Memory check complete")

    if include_disk:
        results["checks"]["disk"] = check_disk()
        statuses.append(results["checks"]["disk"]["status"])
        if verbose:
            print("[INFO] Disk check complete")

    if include_services:
        results["checks"]["services"] = check_services()
        statuses.append(results["checks"]["services"]["status"])
        if verbose:
            print("[INFO] Services check complete")

    if include_caddy:
        results["checks"]["caddy"] = check_caddy()
        statuses.append(results["checks"]["caddy"]["status"])
        if verbose:
            print("[INFO] Caddy check complete")

    if include_ports:
        results["checks"]["ports"] = check_ports()
        statuses.append(results["checks"]["ports"]["status"])
        if verbose:
            print("[INFO] Ports check complete")

    # Determine overall status
    if "critical" in statuses or "error" in statuses:
        results["overall_status"] = "critical"
    elif "warning" in statuses:
        results["overall_status"] = "warning"
    else:
        results["overall_status"] = "ok"

    return results


def format_report(results: dict, format_type: str = "summary") -> str:
    """Format health check results."""

    if format_type == "json":
        return json.dumps(results, indent=2)

    # Summary format
    status_icons = {
        "ok": "✓",
        "warning": "⚠",
        "critical": "✗",
        "error": "!",
        "unknown": "?",
    }

    lines = [
        "=" * 50,
        "SYSTEM HEALTH REPORT",
        "=" * 50,
        f"Overall Status: {status_icons.get(results['overall_status'], '?')} {results['overall_status'].upper()}",
        "",
    ]

    for check_name, check_data in results.get("checks", {}).items():
        status = check_data.get("status", "unknown")
        icon = status_icons.get(status, "?")

        lines.append(f"{icon} {check_name.upper()}")
        lines.append("-" * 30)

        if check_name == "cpu":
            lines.append(f"  Usage: {check_data.get('usage_pct', 'N/A')}%")

        elif check_name == "memory":
            lines.append(
                f"  Used: {check_data.get('used_mb', 'N/A')}MB / {check_data.get('total_mb', 'N/A')}MB ({check_data.get('usage_pct', 'N/A')}%)"
            )
            lines.append(f"  Available: {check_data.get('available_mb', 'N/A')}MB")

        elif check_name == "disk":
            lines.append(
                f"  Used: {check_data.get('used', 'N/A')} / {check_data.get('total', 'N/A')} ({check_data.get('usage_pct', 'N/A')}%)"
            )
            lines.append(f"  Available: {check_data.get('available', 'N/A')}")

        elif check_name == "services":
            lines.append(f"  Running: {check_data.get('running', 0)}")
            lines.append(f"  Stopped: {check_data.get('stopped', 0)}")
            if check_data.get("error"):
                lines.append(f"  Errors: {check_data.get('error', 0)}")

        elif check_name == "caddy":
            lines.append(f"  Running: {'Yes' if check_data.get('running') else 'No'}")
            lines.append(
                f"  Config Valid: {'Yes' if check_data.get('config_valid') else 'No'}"
            )
            if check_data.get("config_error"):
                lines.append(f"  Error: {check_data.get('config_error')[:100]}")

        elif check_name == "ports":
            lines.append(f"  Listening: {check_data.get('listening', [])}")
            if check_data.get("not_listening"):
                lines.append(f"  Not listening: {check_data.get('not_listening', [])}")

        if check_data.get("error"):
            lines.append(f"  Error: {check_data['error']}")

        lines.append("")

    lines.append("=" * 50)

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Check system health")
    parser.add_argument(
        "target",
        nargs="?",
        default="system",
        choices=["system", "services", "caddy", "resources"],
        help="What to check (default: system - all checks)",
    )
    parser.add_argument("--cpu", action="store_true", help="Check CPU only")
    parser.add_argument("--memory", action="store_true", help="Check memory only")
    parser.add_argument("--disk", action="store_true", help="Check disk only")
    parser.add_argument(
        "--format",
        "-f",
        choices=["summary", "json"],
        default="summary",
        help="Output format (default: summary)",
    )
    parser.add_argument("--output", "-o", help="Save report to file")
    parser.add_argument("--verbose", "-v", action="store_true", help="Show progress")

    args = parser.parse_args()

    # Determine what to check
    specific_checks = args.cpu or args.memory or args.disk

    if specific_checks:
        results = run_health_check(
            include_cpu=args.cpu,
            include_memory=args.memory,
            include_disk=args.disk,
            include_services=False,
            include_caddy=False,
            include_ports=False,
            verbose=args.verbose,
        )
    elif args.target == "services":
        results = run_health_check(
            include_cpu=False,
            include_memory=False,
            include_disk=False,
            include_services=True,
            include_caddy=False,
            include_ports=False,
            verbose=args.verbose,
        )
    elif args.target == "caddy":
        results = run_health_check(
            include_cpu=False,
            include_memory=False,
            include_disk=False,
            include_services=False,
            include_caddy=True,
            include_ports=True,
            verbose=args.verbose,
        )
    elif args.target == "resources":
        results = run_health_check(
            include_cpu=True,
            include_memory=True,
            include_disk=True,
            include_services=False,
            include_caddy=False,
            include_ports=False,
            verbose=args.verbose,
        )
    else:
        results = run_health_check(verbose=args.verbose)

    # Format output
    output = format_report(results, args.format)

    if args.output:
        Path(args.output).write_text(output)
        print(f"Report saved to: {args.output}")
        print(f"Overall status: {results['overall_status'].upper()}")
    else:
        print(output)

    # Exit code based on status
    if results["overall_status"] == "critical":
        sys.exit(2)
    elif results["overall_status"] == "warning":
        sys.exit(1)


if __name__ == "__main__":
    main()
