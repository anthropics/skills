import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import process from "node:process";
import test, { type TestContext } from "node:test";

import {
  loadCredentials,
  loadWechatExtendConfig,
  resolveAccount,
} from "./wechat-extend-config.ts";

function useCwd(t: TestContext, cwd: string): void {
  const previous = process.cwd();
  process.chdir(cwd);
  t.after(() => {
    process.chdir(previous);
  });
}

function useHome(t: TestContext, home: string): void {
  const previous = process.env.HOME;
  process.env.HOME = home;
  t.after(() => {
    if (previous === undefined) {
      delete process.env.HOME;
      return;
    }
    process.env.HOME = previous;
  });
}

function useWechatEnv(
  t: TestContext,
  values: Partial<Record<"WECHAT_APP_ID" | "WECHAT_APP_SECRET", string | undefined>>,
): void {
  const previous = {
    WECHAT_APP_ID: process.env.WECHAT_APP_ID,
    WECHAT_APP_SECRET: process.env.WECHAT_APP_SECRET,
  };

  if (values.WECHAT_APP_ID === undefined) {
    delete process.env.WECHAT_APP_ID;
  } else {
    process.env.WECHAT_APP_ID = values.WECHAT_APP_ID;
  }

  if (values.WECHAT_APP_SECRET === undefined) {
    delete process.env.WECHAT_APP_SECRET;
  } else {
    process.env.WECHAT_APP_SECRET = values.WECHAT_APP_SECRET;
  }

  t.after(() => {
    if (previous.WECHAT_APP_ID === undefined) {
      delete process.env.WECHAT_APP_ID;
    } else {
      process.env.WECHAT_APP_ID = previous.WECHAT_APP_ID;
    }

    if (previous.WECHAT_APP_SECRET === undefined) {
      delete process.env.WECHAT_APP_SECRET;
    } else {
      process.env.WECHAT_APP_SECRET = previous.WECHAT_APP_SECRET;
    }
  });
}

async function makeTempDir(prefix: string): Promise<string> {
  return fs.mkdtemp(path.join(os.tmpdir(), prefix));
}

async function writeEnvFile(root: string, content: string): Promise<void> {
  const envPath = path.join(root, ".baoyu-skills", ".env");
  await fs.mkdir(path.dirname(envPath), { recursive: true });
  await fs.writeFile(envPath, content);
}

async function writeExtendFile(root: string, content: string): Promise<void> {
  const extendPath = path.join(root, ".baoyu-skills", "baoyu-post-to-wechat", "EXTEND.md");
  await fs.mkdir(path.dirname(extendPath), { recursive: true });
  await fs.writeFile(extendPath, content);
}

function useXdgConfigHome(t: TestContext, value: string | undefined): void {
  const previous = process.env.XDG_CONFIG_HOME;
  if (value === undefined) {
    delete process.env.XDG_CONFIG_HOME;
  } else {
    process.env.XDG_CONFIG_HOME = value;
  }
  t.after(() => {
    if (previous === undefined) {
      delete process.env.XDG_CONFIG_HOME;
      return;
    }
    process.env.XDG_CONFIG_HOME = previous;
  });
}

test("loadCredentials selects the first complete source without mixing values across sources", async (t) => {
  const cwdRoot = await makeTempDir("wechat-creds-cwd-");
  const homeRoot = await makeTempDir("wechat-creds-home-");

  useCwd(t, cwdRoot);
  useHome(t, homeRoot);
  useWechatEnv(t, {
    WECHAT_APP_ID: undefined,
    WECHAT_APP_SECRET: "stale-secret-from-process-env",
  });

  await writeEnvFile(cwdRoot, "WECHAT_APP_ID=cwd-app-id\nWECHAT_APP_SECRET=cwd-app-secret\n");
  await writeEnvFile(homeRoot, "WECHAT_APP_ID=home-app-id\nWECHAT_APP_SECRET=home-app-secret\n");

  const credentials = loadCredentials();

  assert.equal(credentials.appId, "cwd-app-id");
  assert.equal(credentials.appSecret, "cwd-app-secret");
  assert.equal(credentials.source, "<cwd>/.baoyu-skills/.env");
  assert.deepEqual(credentials.skippedSources, [
    "process.env missing WECHAT_APP_ID",
  ]);
});

test("loadCredentials prefers a complete process.env pair over lower-priority files", async (t) => {
  const cwdRoot = await makeTempDir("wechat-creds-cwd-");
  const homeRoot = await makeTempDir("wechat-creds-home-");

  useCwd(t, cwdRoot);
  useHome(t, homeRoot);
  useWechatEnv(t, {
    WECHAT_APP_ID: "env-app-id",
    WECHAT_APP_SECRET: "env-app-secret",
  });

  await writeEnvFile(cwdRoot, "WECHAT_APP_ID=cwd-app-id\nWECHAT_APP_SECRET=cwd-app-secret\n");
  await writeEnvFile(homeRoot, "WECHAT_APP_ID=home-app-id\nWECHAT_APP_SECRET=home-app-secret\n");

  const credentials = loadCredentials();

  assert.equal(credentials.appId, "env-app-id");
  assert.equal(credentials.appSecret, "env-app-secret");
  assert.equal(credentials.source, "process.env");
  assert.deepEqual(credentials.skippedSources, []);
});

test("resolveAccount returns global remote_publish_* values when no account is configured", async (t) => {
  const cwdRoot = await makeTempDir("wechat-extend-cwd-");
  const homeRoot = await makeTempDir("wechat-extend-home-");

  useCwd(t, cwdRoot);
  useHome(t, homeRoot);
  useXdgConfigHome(t, undefined);

  await writeExtendFile(
    cwdRoot,
    [
      "default_publish_method: remote-api",
      "remote_publish_host: bastion.example.com",
      "remote_publish_user: deploy",
      "remote_publish_port: 2222",
      "remote_publish_identity_file: /home/me/.ssh/id_ed25519",
      "remote_publish_known_hosts_file: /home/me/.ssh/known_hosts",
      "remote_publish_strict_host_key_checking: accept-new",
      "remote_publish_connect_timeout: 12",
      "remote_publish_proxy_jump: jump.example.com",
    ].join("\n"),
  );

  const config = loadWechatExtendConfig();
  const resolved = resolveAccount(config);

  assert.equal(resolved.default_publish_method, "remote-api");
  assert.equal(resolved.remote_publish_host, "bastion.example.com");
  assert.equal(resolved.remote_publish_user, "deploy");
  assert.equal(resolved.remote_publish_port, 2222);
  assert.equal(resolved.remote_publish_identity_file, "/home/me/.ssh/id_ed25519");
  assert.equal(resolved.remote_publish_known_hosts_file, "/home/me/.ssh/known_hosts");
  assert.equal(resolved.remote_publish_strict_host_key_checking, "accept-new");
  assert.equal(resolved.remote_publish_connect_timeout, 12);
  assert.equal(resolved.remote_publish_proxy_jump, "jump.example.com");
});

test("resolveAccount lets account-level remote_publish_* override globals", async (t) => {
  const cwdRoot = await makeTempDir("wechat-extend-cwd-");
  const homeRoot = await makeTempDir("wechat-extend-home-");

  useCwd(t, cwdRoot);
  useHome(t, homeRoot);
  useXdgConfigHome(t, undefined);

  await writeExtendFile(
    cwdRoot,
    [
      "default_publish_method: browser",
      "remote_publish_host: global.example.com",
      "remote_publish_user: deploy",
      "remote_publish_port: 22",
      "accounts:",
      "  - name: Primary",
      "    alias: primary",
      "    default: true",
      "    remote_publish_host: primary.example.com",
      "    remote_publish_user: primary-user",
      "    remote_publish_port: 2200",
      "    remote_publish_identity_file: /p/id_primary",
      "  - name: Secondary",
      "    alias: secondary",
      "    remote_publish_proxy_jump: jump.example.com",
    ].join("\n"),
  );

  const config = loadWechatExtendConfig();
  const primary = resolveAccount(config, "primary");
  assert.equal(primary.alias, "primary");
  assert.equal(primary.remote_publish_host, "primary.example.com");
  assert.equal(primary.remote_publish_user, "primary-user");
  assert.equal(primary.remote_publish_port, 2200);
  assert.equal(primary.remote_publish_identity_file, "/p/id_primary");
  assert.equal(primary.remote_publish_proxy_jump, undefined);

  const secondary = resolveAccount(config, "secondary");
  assert.equal(secondary.alias, "secondary");
  assert.equal(secondary.remote_publish_host, "global.example.com");
  assert.equal(secondary.remote_publish_user, "deploy");
  assert.equal(secondary.remote_publish_port, 22);
  assert.equal(secondary.remote_publish_proxy_jump, "jump.example.com");
});

test("loadWechatExtendConfig throws on invalid remote_publish_port", async (t) => {
  const cwdRoot = await makeTempDir("wechat-extend-cwd-");
  const homeRoot = await makeTempDir("wechat-extend-home-");

  useCwd(t, cwdRoot);
  useHome(t, homeRoot);
  useXdgConfigHome(t, undefined);

  await writeExtendFile(
    cwdRoot,
    [
      "remote_publish_host: example.com",
      "remote_publish_port: 99999",
    ].join("\n"),
  );

  assert.throws(() => loadWechatExtendConfig(), /Invalid remote_publish_port: 99999/);
});

test("loadWechatExtendConfig throws on invalid remote_publish_connect_timeout", async (t) => {
  const cwdRoot = await makeTempDir("wechat-extend-cwd-");
  const homeRoot = await makeTempDir("wechat-extend-home-");

  useCwd(t, cwdRoot);
  useHome(t, homeRoot);
  useXdgConfigHome(t, undefined);

  await writeExtendFile(
    cwdRoot,
    [
      "remote_publish_host: example.com",
      "remote_publish_connect_timeout: 0",
    ].join("\n"),
  );

  assert.throws(() => loadWechatExtendConfig(), /Invalid remote_publish_connect_timeout: 0/);
});

test("loadWechatExtendConfig throws on invalid remote_publish_strict_host_key_checking", async (t) => {
  const cwdRoot = await makeTempDir("wechat-extend-cwd-");
  const homeRoot = await makeTempDir("wechat-extend-home-");

  useCwd(t, cwdRoot);
  useHome(t, homeRoot);
  useXdgConfigHome(t, undefined);

  await writeExtendFile(
    cwdRoot,
    [
      "remote_publish_host: example.com",
      "remote_publish_strict_host_key_checking: maybe",
    ].join("\n"),
  );

  assert.throws(
    () => loadWechatExtendConfig(),
    /Invalid remote_publish_strict_host_key_checking: maybe/,
  );
});

test("loadCredentials reports skipped incomplete sources when no complete pair exists", async (t) => {
  const cwdRoot = await makeTempDir("wechat-creds-cwd-");
  const homeRoot = await makeTempDir("wechat-creds-home-");

  useCwd(t, cwdRoot);
  useHome(t, homeRoot);
  useWechatEnv(t, {
    WECHAT_APP_ID: "env-app-id",
    WECHAT_APP_SECRET: undefined,
  });

  await writeEnvFile(cwdRoot, "WECHAT_APP_SECRET=cwd-app-secret\n");

  assert.throws(
    () => loadCredentials(),
    /Incomplete credential sources skipped:\n- process\.env missing WECHAT_APP_SECRET\n- <cwd>\/\.baoyu-skills\/\.env missing WECHAT_APP_ID/,
  );
});
