#!/usr/bin/env python3
"""
MCP App Development Server Manager

Manages both the Next.js frontend and MCP server for local development.
Provides hot-reload capability and coordinated startup/shutdown.

Usage:
    python dev_server.py --frontend-port 3000 --mcp-port 8080
    python dev_server.py --help
"""

import argparse
import asyncio
import os
import signal
import subprocess
import sys
from pathlib import Path
from typing import Optional


class DevServerManager:
    """Manages frontend and MCP server processes."""

    def __init__(
        self,
        frontend_port: int = 3000,
        mcp_port: int = 8080,
        frontend_cmd: str = "npm run dev",
        mcp_cmd: str = "npx ts-node server/index.ts",
    ):
        self.frontend_port = frontend_port
        self.mcp_port = mcp_port
        self.frontend_cmd = frontend_cmd
        self.mcp_cmd = mcp_cmd
        self.processes: list[subprocess.Popen] = []
        self._shutdown_event = asyncio.Event()

    async def wait_for_port(
        self, port: int, timeout: float = 30.0, interval: float = 0.5
    ) -> bool:
        """Wait for a port to become available."""
        import socket

        elapsed = 0.0
        while elapsed < timeout:
            try:
                with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                    s.settimeout(1)
                    s.connect(("localhost", port))
                    return True
            except (socket.error, socket.timeout):
                await asyncio.sleep(interval)
                elapsed += interval
        return False

    def start_process(
        self, cmd: str, name: str, env: Optional[dict] = None
    ) -> subprocess.Popen:
        """Start a subprocess with proper configuration."""
        process_env = os.environ.copy()
        if env:
            process_env.update(env)

        print(f"[{name}] Starting: {cmd}")

        process = subprocess.Popen(
            cmd,
            shell=True,
            env=process_env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )

        self.processes.append(process)
        return process

    async def stream_output(self, process: subprocess.Popen, name: str):
        """Stream process output with prefix."""
        if process.stdout:
            for line in process.stdout:
                print(f"[{name}] {line.rstrip()}")

    async def start(self):
        """Start all development servers."""
        print("=" * 60)
        print("MCP App Development Server")
        print("=" * 60)
        print(f"Frontend: http://localhost:{self.frontend_port}")
        print(f"MCP Server: http://localhost:{self.mcp_port}")
        print("=" * 60)
        print()

        # Start MCP server first
        mcp_env = {"MCP_PORT": str(self.mcp_port)}
        mcp_process = self.start_process(self.mcp_cmd, "MCP", mcp_env)

        # Wait for MCP server to be ready
        print("[MCP] Waiting for server to start...")
        if await self.wait_for_port(self.mcp_port):
            print(f"[MCP] Server ready on port {self.mcp_port}")
        else:
            print("[MCP] Warning: Server did not start within timeout")

        # Start frontend
        frontend_env = {
            "PORT": str(self.frontend_port),
            "NEXT_PUBLIC_MCP_URL": f"http://localhost:{self.mcp_port}",
        }
        frontend_process = self.start_process(self.frontend_cmd, "Frontend", frontend_env)

        # Stream output from both processes
        await asyncio.gather(
            self.stream_output(mcp_process, "MCP"),
            self.stream_output(frontend_process, "Frontend"),
            self._wait_for_shutdown(),
        )

    async def _wait_for_shutdown(self):
        """Wait for shutdown signal."""
        await self._shutdown_event.wait()

    def shutdown(self):
        """Gracefully shutdown all processes."""
        print("\nShutting down servers...")
        self._shutdown_event.set()

        for process in self.processes:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill()

        print("All servers stopped.")


def main():
    parser = argparse.ArgumentParser(
        description="MCP App Development Server Manager"
    )
    parser.add_argument(
        "--frontend-port",
        type=int,
        default=3000,
        help="Frontend server port (default: 3000)",
    )
    parser.add_argument(
        "--mcp-port",
        type=int,
        default=8080,
        help="MCP server port (default: 8080)",
    )
    parser.add_argument(
        "--frontend-cmd",
        type=str,
        default="npm run dev",
        help="Frontend start command",
    )
    parser.add_argument(
        "--mcp-cmd",
        type=str,
        default="npx ts-node server/index.ts",
        help="MCP server start command",
    )

    args = parser.parse_args()

    manager = DevServerManager(
        frontend_port=args.frontend_port,
        mcp_port=args.mcp_port,
        frontend_cmd=args.frontend_cmd,
        mcp_cmd=args.mcp_cmd,
    )

    # Handle signals
    def signal_handler(sig, frame):
        manager.shutdown()
        sys.exit(0)

    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    # Run the server manager
    try:
        asyncio.run(manager.start())
    except KeyboardInterrupt:
        manager.shutdown()


if __name__ == "__main__":
    main()
