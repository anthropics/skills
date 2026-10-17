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

import atexit
import os
import signal
import socket
import subprocess
import sys
import time
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


def stop_servers(server_processes):
    """Stop all servers, killing the whole process group of each one.

    Because servers are started with shell=True (e.g. "npm run dev"), the
    direct child is a shell that spawns further children (npm -> node/vite).
    Signalling only the direct child leaves those grandchildren running and
    they get orphaned (reparented to init/systemd). Sending the signal to the
    process group instead tears down the entire tree.

    The shell exiting is not proof that the group is gone: it may have
    backgrounded the server, or a descendant may ignore SIGTERM. So the group
    itself is checked and signalled, independently of the shell's lifetime.
    """
    if not server_processes:
        return
    print(f"\nStopping {len(server_processes)} server(s)...")
    for process in server_processes:
        _signal_group(process, signal.SIGTERM)
    for i, process in enumerate(server_processes):
        if not _wait_group(process, timeout=5):
            _signal_group(process, signal.SIGKILL)
            if not _wait_group(process, timeout=5):
                print(f"Warning: server {i+1} process group {process.pid} did not exit")
                continue
        print(f"Server {i+1} stopped")
    server_processes.clear()
    print("All servers stopped")


# Each server is started with start_new_session=True, so its process group ID
# is the shell's PID. The ID stays valid after the shell exits: a PID is not
# reused while a process group with that ID still has members.

def _group_alive(process):
    # Reap the shell first, otherwise its zombie keeps the group "alive".
    process.poll()
    try:
        os.killpg(process.pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _wait_group(process, timeout):
    """Wait until every process in the server's group has exited."""
    deadline = time.monotonic() + timeout
    while _group_alive(process):
        if time.monotonic() >= deadline:
            return False
        time.sleep(0.1)
    return True


def _signal_group(process, sig):
    """Send a signal to the server's whole process group."""
    process.poll()
    try:
        os.killpg(process.pid, sig)
    except (ProcessLookupError, PermissionError):
        pass


def _install_cleanup_handlers(server_processes):
    """Ensure servers are stopped even if this wrapper is interrupted
    (SIGINT/SIGTERM/SIGHUP) or exits unexpectedly."""
    def handler(signum, frame):
        stop_servers(server_processes)
        sys.exit(128 + signum)

    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        try:
            signal.signal(signum, handler)
        except (ValueError, OSError):
            pass

    atexit.register(stop_servers, server_processes)


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
    _install_cleanup_handlers(server_processes)

    try:
        # Start all servers
        for i, server in enumerate(servers):
            print(f"Starting server {i+1}/{len(servers)}: {server['cmd']}")

            # Use shell=True to support commands with cd and &&.
            # start_new_session=True puts each server in its own process group
            # so the whole tree (sh -> npm -> node/vite) can be killed on exit.
            # stdout/stderr are inherited (not piped) so a chatty server cannot
            # fill an undrained pipe buffer and deadlock.
            process = subprocess.Popen(
                server['cmd'],
                shell=True,
                start_new_session=True,
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
        stop_servers(server_processes)


if __name__ == '__main__':
    main()
