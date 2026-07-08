#!/usr/bin/env python3
"""
Start one or more servers, wait for them to be ready, run a command, then clean up.

Usage:
    # Single server
    python scripts/with_server.py --server "npm run dev" --port 5173 -- python automation.py
    python scripts/with_server.py --server "npm start" --port 3000 -- python test.py

    # Multiple servers
    python scripts/with_server.py \
      --server "python server.py" --port 3000 --cwd backend \
      --server "npm run dev" --port 5173 --cwd frontend \
      -- python test.py

    # Legacy "cd <dir> && <cmd>" form is still accepted for backwards compatibility
    python scripts/with_server.py \
      --server "cd backend && python server.py" --port 3000 \
      -- python test.py
"""

import os
import shlex
import subprocess
import socket
import time
import sys
import argparse


def is_server_ready(port, timeout=30):
    """Wait for server to be ready by polling the port."""
    start_time = time.time()
    while time.time() - start_time < timeout:
        try:
            with socket.create_connection(('localhost', port), timeout=1):
                return True
        except (socket.error, ConnectionRefusedError):
            time.sleep(0.5)
    return False


def _parse_server_cmd(cmd, cwd=None):
    """Return (argv, cwd) for a server command string.

    Handles the legacy "cd <dir> && <rest>" pattern so existing invocations
    keep working without shell=True.
    """
    if cwd is None and cmd.startswith("cd "):
        parts = cmd.split(" && ", 1)
        if len(parts) == 2:
            cwd = parts[0][3:].strip()
            cmd = parts[1]
    return shlex.split(cmd), cwd or None


def main():
    parser = argparse.ArgumentParser(description='Run command with one or more servers')
    parser.add_argument('--server', action='append', dest='servers', required=True,
                        help='Server command (can be repeated)')
    parser.add_argument('--port', action='append', dest='ports', type=int, required=True,
                        help='Port for each server (must match --server count)')
    parser.add_argument('--cwd', action='append', dest='cwds', default=[],
                        help='Working directory for each server (optional, repeat to match each --server)')
    parser.add_argument('--timeout', type=int, default=30,
                        help='Timeout in seconds per server (default: 30)')
    parser.add_argument('command', nargs=argparse.REMAINDER,
                        help='Command to run after server(s) ready')

    args = parser.parse_args()

    # Remove the '--' separator if present
    if args.command and args.command[0] == '--':
        args.command = args.command[1:]

    if not args.command:
        print("Error: No command specified to run")
        sys.exit(1)

    if len(args.servers) != len(args.ports):
        print("Error: Number of --server and --port arguments must match")
        sys.exit(1)

    servers = []
    for i, (cmd, port) in enumerate(zip(args.servers, args.ports)):
        explicit_cwd = args.cwds[i] if i < len(args.cwds) else None
        argv, cwd = _parse_server_cmd(cmd, explicit_cwd)
        servers.append({'argv': argv, 'cmd': cmd, 'port': port, 'cwd': cwd})

    server_processes = []

    try:
        for i, server in enumerate(servers):
            print(f"Starting server {i+1}/{len(servers)}: {server['cmd']}")

            process = subprocess.Popen(
                server['argv'],
                cwd=server['cwd'],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            server_processes.append(process)

            print(f"Waiting for server on port {server['port']}...")
            if not is_server_ready(server['port'], timeout=args.timeout):
                raise RuntimeError(
                    f"Server failed to start on port {server['port']} within {args.timeout}s"
                )

            print(f"Server ready on port {server['port']}")

        print(f"\nAll {len(servers)} server(s) ready")

        print(f"Running: {' '.join(args.command)}\n")
        result = subprocess.run(args.command)
        sys.exit(result.returncode)

    finally:
        print(f"\nStopping {len(server_processes)} server(s)...")
        for i, process in enumerate(server_processes):
            try:
                process.terminate()
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            print(f"Server {i+1} stopped")
        print("All servers stopped")


if __name__ == '__main__':
    main()
