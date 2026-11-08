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

Server output is written to a temporary log file (never to an unread pipe, which
would block a chatty server) and the tail of that log is printed if a server fails
to start. Each server runs in its own process group so cleanup also stops the
processes the shell spawned (for example the node process behind `npm run dev`).
"""

import argparse
import os
import signal
import socket
import subprocess
import sys
import tempfile
import time

IS_WINDOWS = os.name == 'nt'
LOG_TAIL_LINES = 40


def is_port_open(port):
    """Return True if something is accepting connections on localhost:port."""
    try:
        with socket.create_connection(('localhost', port), timeout=1):
            return True
    except OSError:
        return False


def is_server_ready(port, timeout=30, process=None):
    """Wait for server to be ready by polling the port.

    If `process` is given and it exits before the port opens, stop waiting
    immediately instead of running out the full timeout.
    """
    start_time = time.time()
    while time.time() - start_time < timeout:
        if process is not None and process.poll() is not None:
            return False
        if is_port_open(port):
            return True
        time.sleep(0.5)
    return False


def tail(path, lines=LOG_TAIL_LINES):
    """Return the last `lines` lines of a text file, or '' if unreadable."""
    try:
        with open(path, 'r', errors='replace') as f:
            return ''.join(f.readlines()[-lines:])
    except OSError:
        return ''


def start_server(cmd, log_file):
    """Start `cmd` through the shell in its own process group, logging to `log_file`."""
    kwargs = {'stdout': log_file, 'stderr': subprocess.STDOUT, 'stdin': subprocess.DEVNULL}
    if IS_WINDOWS:
        kwargs['creationflags'] = subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        kwargs['start_new_session'] = True
    # shell=True so commands with `cd` and `&&` work.
    return subprocess.Popen(cmd, shell=True, **kwargs)


def stop_server(process):
    """Stop the server and everything it spawned."""
    try:
        if IS_WINDOWS:
            subprocess.run(['taskkill', '/F', '/T', '/PID', str(process.pid)],
                           capture_output=True)
        else:
            os.killpg(process.pid, signal.SIGTERM)
    except OSError:
        pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    # The shell may have exited while a child kept running; make sure the group is gone.
    if not IS_WINDOWS:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except OSError:
            pass
    if process.poll() is None:
        process.kill()
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

    servers = [{'cmd': cmd, 'port': port} for cmd, port in zip(args.servers, args.ports)]

    # A stale process on the port would make a failed startup look like success.
    for server in servers:
        if is_port_open(server['port']):
            print(f"Error: port {server['port']} is already in use; stop that process "
                  f"or choose another port")
            sys.exit(1)

    # Turn SIGTERM into a normal exit so the cleanup below still runs.
    if not IS_WINDOWS:
        signal.signal(signal.SIGTERM, lambda signum, frame: sys.exit(128 + signum))

    server_processes = []
    log_dir = tempfile.TemporaryDirectory(prefix='with_server_')
    try:
        # Start all servers
        for i, server in enumerate(servers):
            print(f"Starting server {i+1}/{len(servers)}: {server['cmd']}")

            log_path = os.path.join(log_dir.name, f'server{i+1}.log')
            with open(log_path, 'wb') as log_file:
                process = start_server(server['cmd'], log_file)
            server_processes.append(process)

            # Wait for this server to be ready
            print(f"Waiting for server on port {server['port']}...")
            if not is_server_ready(server['port'], timeout=args.timeout, process=process):
                if process.poll() is not None:
                    reason = f"Server exited with code {process.returncode} before port {server['port']} opened"
                else:
                    reason = f"Server failed to start on port {server['port']} within {args.timeout}s"
                output = tail(log_path)
                if output:
                    reason += f"\n--- last {LOG_TAIL_LINES} lines of server output ---\n{output.rstrip()}\n---"
                raise RuntimeError(reason)

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
            stop_server(process)
            print(f"Server {i+1} stopped")
        print("All servers stopped")
        log_dir.cleanup()


if __name__ == '__main__':
    main()
