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
import os
import signal
import tempfile
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


def read_log_tail(log_path, max_bytes=2048):
    """Return the last chunk of a server log for error reporting."""
    try:
        with open(log_path, 'rb') as f:
            f.seek(0, os.SEEK_END)
            size = f.tell()
            f.seek(max(0, size - max_bytes))
            return f.read().decode('utf-8', errors='replace').strip()
    except OSError:
        return ''


def stop_process_tree(process):
    """Stop a server and any children it spawned (e.g. via shell wrappers)."""
    posix = os.name == 'posix'

    def signal_group(sig, fallback):
        # The server runs in its own process group (start_new_session=True),
        # so signal the whole group: terminating only the shell would orphan
        # the actual server process and leave the port bound.
        if posix:
            try:
                os.killpg(process.pid, sig)
            except ProcessLookupError:
                pass
            return
        fallback()

    signal_group(signal.SIGTERM, process.terminate)
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        signal_group(signal.SIGKILL if posix else signal.SIGTERM, process.kill)
        process.wait()


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

            # Send output to a log file rather than a pipe: nothing reads the
            # pipe while the command runs, so a chatty server would fill the
            # pipe buffer and block mid-run.
            log_fd, log_path = tempfile.mkstemp(
                prefix=f"with_server_port{server['port']}_", suffix='.log'
            )
            print(f"Server log: {log_path}")

            # Use shell=True to support commands with cd and &&.
            # start_new_session puts the shell and everything it spawns in one
            # process group so cleanup can stop all of it.
            process = subprocess.Popen(
                server['cmd'],
                shell=True,
                stdout=log_fd,
                stderr=subprocess.STDOUT,
                start_new_session=True
            )
            os.close(log_fd)
            server_processes.append(process)

            # Wait for this server to be ready
            print(f"Waiting for server on port {server['port']}...")
            if not is_server_ready(server['port'], timeout=args.timeout):
                message = f"Server failed to start on port {server['port']} within {args.timeout}s"
                log_tail = read_log_tail(log_path)
                if log_tail:
                    message += f"\nLast server output:\n{log_tail}"
                raise RuntimeError(message)

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
            stop_process_tree(process)
            print(f"Server {i+1} stopped")
        print("All servers stopped")


if __name__ == '__main__':
    main()
