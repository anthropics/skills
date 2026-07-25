import assert from "node:assert/strict";
import net from "node:net";
import test from "node:test";

import {
  buildSshArgs,
  findFreePort,
  normalizeRemoteConfig,
} from "./wechat-remote-publish.ts";

test("normalizeRemoteConfig requires a host", () => {
  assert.throws(
    () => normalizeRemoteConfig({ host: "" }),
    /Remote publish host is required/,
  );
  assert.throws(
    () => normalizeRemoteConfig({ host: "   " }),
    /Remote publish host is required/,
  );
});

test("normalizeRemoteConfig applies user/port defaults and trims host", () => {
  const result = normalizeRemoteConfig({ host: "  example.com  " });
  assert.equal(result.host, "example.com");
  assert.equal(result.user, "root");
  assert.equal(result.port, 22);
  assert.equal(result.identityFile, undefined);
  assert.equal(result.knownHostsFile, undefined);
  assert.equal(result.strictHostKeyChecking, undefined);
  assert.equal(result.connectTimeout, undefined);
  assert.equal(result.proxyJump, undefined);
});

test("normalizeRemoteConfig preserves explicit user, port, and SSH options", () => {
  const result = normalizeRemoteConfig({
    host: "example.com",
    user: "deploy",
    port: 2222,
    identityFile: "/home/me/.ssh/id_ed25519",
    knownHostsFile: "/home/me/.ssh/known_hosts",
    strictHostKeyChecking: "accept-new",
    connectTimeout: 15,
    proxyJump: "bastion.example.com",
  });
  assert.equal(result.user, "deploy");
  assert.equal(result.port, 2222);
  assert.equal(result.identityFile, "/home/me/.ssh/id_ed25519");
  assert.equal(result.knownHostsFile, "/home/me/.ssh/known_hosts");
  assert.equal(result.strictHostKeyChecking, "accept-new");
  assert.equal(result.connectTimeout, 15);
  assert.equal(result.proxyJump, "bastion.example.com");
});

test("normalizeRemoteConfig rejects invalid port", () => {
  assert.throws(
    () => normalizeRemoteConfig({ host: "example.com", port: 0 }),
    /Invalid remote publish port/,
  );
  assert.throws(
    () => normalizeRemoteConfig({ host: "example.com", port: 65536 }),
    /Invalid remote publish port/,
  );
  assert.throws(
    () => normalizeRemoteConfig({ host: "example.com", port: 1.5 }),
    /Invalid remote publish port/,
  );
});

test("normalizeRemoteConfig rejects invalid connect timeout", () => {
  assert.throws(
    () => normalizeRemoteConfig({ host: "example.com", connectTimeout: 0 }),
    /Invalid remote_publish_connect_timeout/,
  );
  assert.throws(
    () => normalizeRemoteConfig({ host: "example.com", connectTimeout: -3 }),
    /Invalid remote_publish_connect_timeout/,
  );
});

test("normalizeRemoteConfig rejects invalid strict host key checking", () => {
  assert.throws(
    () =>
      normalizeRemoteConfig({
        host: "example.com",
        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        strictHostKeyChecking: "maybe" as any,
      }),
    /Invalid remote_publish_strict_host_key_checking/,
  );
});

test("normalizeRemoteConfig falls back to default user when blank string provided", () => {
  const result = normalizeRemoteConfig({ host: "example.com", user: "   " });
  assert.equal(result.user, "root");
});

test("buildSshArgs emits the whitelisted minimum set", () => {
  const args = buildSshArgs(
    { host: "example.com", user: "root", port: 22 },
    1080,
  );
  assert.deepEqual(args, [
    "-N",
    "-T",
    "-D", "127.0.0.1:1080",
    "-o", "ExitOnForwardFailure=yes",
    "-o", "ServerAliveInterval=30",
    "-o", "ServerAliveCountMax=3",
    "-p", "22",
    "root@example.com",
  ]);
});

test("buildSshArgs threads optional ssh options in stable order", () => {
  const args = buildSshArgs(
    {
      host: "example.com",
      user: "deploy",
      port: 2222,
      identityFile: "/p/id_ed25519",
      knownHostsFile: "/p/known_hosts",
      strictHostKeyChecking: "accept-new",
      connectTimeout: 12,
      proxyJump: "bastion.example.com",
    },
    1080,
  );
  assert.deepEqual(args, [
    "-N",
    "-T",
    "-D", "127.0.0.1:1080",
    "-o", "ExitOnForwardFailure=yes",
    "-o", "ServerAliveInterval=30",
    "-o", "ServerAliveCountMax=3",
    "-p", "2222",
    "-i", "/p/id_ed25519",
    "-o", "UserKnownHostsFile=/p/known_hosts",
    "-o", "StrictHostKeyChecking=accept-new",
    "-o", "ConnectTimeout=12",
    "-J", "bastion.example.com",
    "deploy@example.com",
  ]);
});

test("buildSshArgs does not emit raw ssh options for unknown fields", () => {
  const args = buildSshArgs(
    {
      host: "example.com",
      user: "root",
      port: 22,
      // No extra unknown keys are accepted — typed config is the whitelist.
    },
    1080,
  );
  assert.equal(
    args.filter((a) => a === "-o" || a.startsWith("--")).length,
    3, // ExitOnForwardFailure, ServerAliveInterval, ServerAliveCountMax (and only those)
    "buildSshArgs must only emit the three baseline -o options when no extras given",
  );
});

test("buildSshArgs rejects invalid SOCKS port", () => {
  assert.throws(
    () => buildSshArgs({ host: "example.com", user: "root", port: 22 }, 0),
    /Invalid SOCKS port/,
  );
  assert.throws(
    () => buildSshArgs({ host: "example.com", user: "root", port: 22 }, 70_000),
    /Invalid SOCKS port/,
  );
});

test("findFreePort returns a usable loopback port", async () => {
  const port = await findFreePort();
  assert.ok(port > 0 && port < 65536, `expected valid port, got ${port}`);

  await new Promise<void>((resolve, reject) => {
    const server = net.createServer();
    server.unref();
    server.once("error", reject);
    server.listen(port, "127.0.0.1", () => {
      server.close((err) => (err ? reject(err) : resolve()));
    });
  });
});
