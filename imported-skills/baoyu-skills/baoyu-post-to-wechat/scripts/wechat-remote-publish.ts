import { spawn, type ChildProcessByStdio } from "node:child_process";
import net from "node:net";
import type { Readable } from "node:stream";

import type { StrictHostKeyChecking } from "./wechat-extend-config.ts";
import type { WechatClient } from "./wechat-http.ts";
import { createSocksClient } from "./wechat-socks-http.ts";

export interface RemotePublishConfig {
  host: string;
  user?: string;
  port?: number;
  identityFile?: string;
  knownHostsFile?: string;
  strictHostKeyChecking?: StrictHostKeyChecking;
  connectTimeout?: number;
  proxyJump?: string;
}

export interface NormalizedRemotePublishConfig {
  host: string;
  user: string;
  port: number;
  identityFile?: string;
  knownHostsFile?: string;
  strictHostKeyChecking?: StrictHostKeyChecking;
  connectTimeout?: number;
  proxyJump?: string;
}

export interface SshTunnel {
  port: number;
  client: WechatClient;
  close: () => Promise<void>;
}

export interface StartSshTunnelOptions {
  readyTimeoutMs?: number;
  killTimeoutMs?: number;
}

const DEFAULT_USER = "root";
const DEFAULT_PORT = 22;
const DEFAULT_READY_TIMEOUT_MS = 10_000;
const DEFAULT_KILL_TIMEOUT_MS = 3_000;
const SSH_LOOPBACK_HOST = "127.0.0.1";

export function normalizeRemoteConfig(config: RemotePublishConfig): NormalizedRemotePublishConfig {
  if (!config.host || !config.host.trim()) {
    throw new Error("Remote publish host is required (set remote_publish_host or --remote-host).");
  }

  const port = config.port ?? DEFAULT_PORT;
  if (!Number.isInteger(port) || port < 1 || port > 65535) {
    throw new Error(`Invalid remote publish port: ${config.port}`);
  }

  if (config.connectTimeout !== undefined) {
    if (!Number.isInteger(config.connectTimeout) || config.connectTimeout <= 0) {
      throw new Error(`Invalid remote_publish_connect_timeout: ${config.connectTimeout}`);
    }
  }

  if (
    config.strictHostKeyChecking !== undefined &&
    config.strictHostKeyChecking !== "yes" &&
    config.strictHostKeyChecking !== "no" &&
    config.strictHostKeyChecking !== "accept-new"
  ) {
    throw new Error(`Invalid remote_publish_strict_host_key_checking: ${config.strictHostKeyChecking}`);
  }

  return {
    host: config.host.trim(),
    user: (config.user ?? DEFAULT_USER).trim() || DEFAULT_USER,
    port,
    identityFile: config.identityFile,
    knownHostsFile: config.knownHostsFile,
    strictHostKeyChecking: config.strictHostKeyChecking,
    connectTimeout: config.connectTimeout,
    proxyJump: config.proxyJump,
  };
}

export function buildSshArgs(config: NormalizedRemotePublishConfig, socksPort: number): string[] {
  if (!Number.isInteger(socksPort) || socksPort < 1 || socksPort > 65535) {
    throw new Error(`Invalid SOCKS port: ${socksPort}`);
  }

  const args: string[] = [
    "-N",
    "-T",
    "-D", `${SSH_LOOPBACK_HOST}:${socksPort}`,
    "-o", "ExitOnForwardFailure=yes",
    "-o", "ServerAliveInterval=30",
    "-o", "ServerAliveCountMax=3",
    "-p", String(config.port),
  ];

  if (config.identityFile) {
    args.push("-i", config.identityFile);
  }
  if (config.knownHostsFile) {
    args.push("-o", `UserKnownHostsFile=${config.knownHostsFile}`);
  }
  if (config.strictHostKeyChecking) {
    args.push("-o", `StrictHostKeyChecking=${config.strictHostKeyChecking}`);
  }
  if (config.connectTimeout !== undefined) {
    args.push("-o", `ConnectTimeout=${config.connectTimeout}`);
  }
  if (config.proxyJump) {
    args.push("-J", config.proxyJump);
  }

  args.push(`${config.user}@${config.host}`);
  return args;
}

export async function findFreePort(): Promise<number> {
  return new Promise<number>((resolve, reject) => {
    const server = net.createServer();
    server.unref();
    server.on("error", reject);
    server.listen(0, SSH_LOOPBACK_HOST, () => {
      const address = server.address();
      if (!address || typeof address === "string") {
        server.close(() => reject(new Error("Failed to acquire free port")));
        return;
      }
      const port = address.port;
      server.close((err) => {
        if (err) reject(err);
        else resolve(port);
      });
    });
  });
}

export async function waitForSocksReady(port: number, timeoutMs: number): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  let lastError: unknown = undefined;

  while (Date.now() < deadline) {
    try {
      await tryConnect(port);
      return;
    } catch (err) {
      lastError = err;
      await sleep(150);
    }
  }
  throw new Error(`SOCKS proxy on ${SSH_LOOPBACK_HOST}:${port} not ready within ${timeoutMs}ms${lastError ? `: ${(lastError as Error).message}` : ""}`);
}

function tryConnect(port: number): Promise<void> {
  return new Promise((resolve, reject) => {
    const socket = net.connect({ host: SSH_LOOPBACK_HOST, port });
    socket.once("connect", () => {
      socket.destroy();
      resolve();
    });
    socket.once("error", (err) => {
      socket.destroy();
      reject(err);
    });
  });
}

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

export async function startSshTunnel(
  config: NormalizedRemotePublishConfig,
  options: StartSshTunnelOptions = {},
): Promise<SshTunnel> {
  const readyTimeout = options.readyTimeoutMs ?? DEFAULT_READY_TIMEOUT_MS;
  const killTimeout = options.killTimeoutMs ?? DEFAULT_KILL_TIMEOUT_MS;

  const port = await findFreePort();
  const args = buildSshArgs(config, port);

  console.error(`[wechat-remote-publish] Starting SSH SOCKS5 tunnel: ssh ${args.join(" ")}`);
  const child = spawn("ssh", args, {
    stdio: ["ignore", "pipe", "pipe"],
  }) as ChildProcessByStdio<null, Readable, Readable>;

  const stderrChunks: string[] = [];
  child.stderr.on("data", (chunk: Buffer) => {
    stderrChunks.push(chunk.toString("utf-8"));
  });

  let earlyExit: { code: number | null; signal: NodeJS.Signals | null } | undefined;
  child.once("exit", (code, signal) => {
    earlyExit = { code, signal };
  });

  try {
    await waitForSocksReady(port, readyTimeout);
  } catch (err) {
    await killChild(child, killTimeout);
    const stderrTail = stderrChunks.join("").trim().split("\n").slice(-5).join("\n");
    const suffix = stderrTail ? `\nssh stderr (tail):\n${stderrTail}` : "";
    const exitSuffix = earlyExit
      ? `\nssh exited early with code=${earlyExit.code} signal=${earlyExit.signal}`
      : "";
    throw new Error(`${(err as Error).message}${exitSuffix}${suffix}`);
  }

  const client = createSocksClient({ host: SSH_LOOPBACK_HOST, port });

  const signalHandlers: Array<{ signal: NodeJS.Signals; handler: () => void }> = [];
  let closed = false;
  const close = async (): Promise<void> => {
    if (closed) return;
    closed = true;
    for (const { signal, handler } of signalHandlers) {
      process.off(signal, handler);
    }
    await killChild(child, killTimeout);
  };

  for (const signal of ["SIGINT", "SIGTERM", "SIGHUP"] as const) {
    const handler = () => {
      void close();
    };
    process.once(signal, handler);
    signalHandlers.push({ signal, handler });
  }

  return { port, client, close };
}

async function killChild(child: ChildProcessByStdio<null, Readable, Readable>, killTimeoutMs: number): Promise<void> {
  if (child.exitCode !== null || child.signalCode !== null) {
    return;
  }
  const exited = new Promise<void>((resolve) => {
    child.once("exit", () => resolve());
  });
  try {
    child.kill("SIGTERM");
  } catch {
    /* already dead */
  }

  const timer = setTimeout(() => {
    try {
      child.kill("SIGKILL");
    } catch {
      /* already dead */
    }
  }, killTimeoutMs);

  try {
    await exited;
  } finally {
    clearTimeout(timer);
  }
}

export async function withSshTunnel<T>(
  config: NormalizedRemotePublishConfig,
  fn: (client: WechatClient) => Promise<T>,
  options?: StartSshTunnelOptions,
): Promise<T> {
  const tunnel = await startSshTunnel(config, options);
  try {
    return await fn(tunnel.client);
  } finally {
    await tunnel.close();
  }
}
