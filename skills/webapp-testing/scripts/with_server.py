#!/usr/bin/env python3
"""
Start one or more servers, wait for them to be ready, run a command, then clean up.

Usage:
    # Single server
    python scripts/with_server.py --server "npm run dev" --port 5173 -- python automation.py
    python scripts/with_server.py --server "npm start" --port 3000 -- python test.py

    # Multiple servers
    python scripts/with_server.py \
      --server "cd backend && python server.py" --port 3000 \
      --server "cd frontend && npm run dev" --port 5173 \
      -- python test.py
"""

import subprocess
import socket
import time
import sys
import argparse
import os
import re
import shlex


def parse_server_command(cmd_str: str) -> tuple[list[str], str | None, dict[str, str]]:
    """Parse a server command into argv tokens, an optional working directory,
    and a dict of environment variable assignments.

    Supports patterns like:
      "cd backend && python server.py"
      "PORT=8080 python server.py"
      "cd backend && PORT=8080 NODE_ENV=dev python server.py"
    without invoking shell=True.

    Leading NAME=value tokens are extracted into an env dict so they can be
    passed via the ``env`` parameter of ``subprocess.Popen`` instead of being
    mistaken for the executable name.
    """
    tokens = shlex.split(cmd_str)
    cwd_dir: str | None = None

    # Handle optional "cd <dir> &&" prefix
    if len(tokens) >= 4 and tokens[0] == "cd" and tokens[2] == "&&":
        cwd_dir = tokens[1]
        tokens = tokens[3:]

    # Extract leading NAME=value environment assignments
    env_vars: dict[str, str] = {}
    _env_re = re.compile(r'^([A-Za-z_][A-Za-z0-9_]*)=(.*)$')
    while tokens:
        m = _env_re.match(tokens[0])
        if m:
            env_vars[m.group(1)] = m.group(2)
            tokens = tokens[1:]
        else:
            break

    return tokens, cwd_dir, env_vars

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


def main():
    parser = argparse.ArgumentParser(description='Run command with one or more servers')
    parser.add_argument('--server', action='append', dest='servers', required=True, help='Server command (can be repeated)')
    parser.add_argument('--port', action='append', dest='ports', type=int, required=True, help='Port for each server (must match --server count)')
    parser.add_argument('--timeout', type=int, default=30, help='Timeout in seconds per server (default: 30)')
    parser.add_argument('command', nargs=argparse.REMAINDER, help='Command to run after server(s) ready')

    args = parser.parse_args()

    # Remove the '--' separator if present
    if args.command and args.command[0] == '--':
        args.command = args.command[1:]

    if not args.command:
        print("Error: No command specified to run")
        sys.exit(1)

    # Parse server configurations
    if len(args.servers) != len(args.ports):
        print("Error: Number of --server and --port arguments must match")
        sys.exit(1)

    servers = []
    for cmd, port in zip(args.servers, args.ports):
        servers.append({'cmd': cmd, 'port': port})

    server_processes = []

    try:
        # Start all servers
        for i, server in enumerate(servers):
            print(f"Starting server {i+1}/{len(servers)}: {server['cmd']}")

            argv, cwd, env_vars = parse_server_command(server['cmd'])

            # Merge any leading NAME=value assignments into a copy of the
            # current environment so the child process sees them, just as a
            # shell would.
            popen_env = None
            if env_vars:
                popen_env = os.environ.copy()
                popen_env.update(env_vars)

            process = subprocess.Popen(
                argv,
                cwd=cwd,
                env=popen_env,
                shell=False,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE
            )
            server_processes.append(process)

            # Wait for this server to be ready
            print(f"Waiting for server on port {server['port']}...")
            if not is_server_ready(server['port'], timeout=args.timeout):
                raise RuntimeError(f"Server failed to start on port {server['port']} within {args.timeout}s")

            print(f"Server ready on port {server['port']}")

        print(f"\nAll {len(servers)} server(s) ready")

        # Run the command
        print(f"Running: {' '.join(args.command)}\n")
        result = subprocess.run(args.command)
        sys.exit(result.returncode)

    finally:
        # Clean up all servers
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