#!/usr/bin/env node

// Usage: node send.mjs --title "..." --message "..." [--urgent] [--successed]
// Provider is auto-detected from environment variables (NTFY_URL or BARK_URL).

const args = process.argv.slice(2);

function getArg(name) {
  const idx = args.indexOf(`--${name}`);
  return idx !== -1 && idx + 1 < args.length ? args[idx + 1] : undefined;
}

function hasFlag(name) {
  return args.includes(`--${name}`);
}

// Collect all configured providers
const providers = [];
if (process.env.NTFY_URL) providers.push("ntfy");
if (process.env.BARK_URL) providers.push("bark");

if (providers.length === 0) {
  console.error(`Error: No notification service configured. Set at least one environment variable:

  ntfy (cross-platform):
    export NTFY_URL="https://ntfy.sh/your-topic"
    export NTFY_TOKEN="tk_xxx"          # optional, for private servers

  Bark (iOS):
    export BARK_URL="https://api.day.app/your_device_key"

Set these in your shell profile, .env, or Claude Code settings (env field in settings.json).`);
  process.exit(1);
}

const title = getArg("title") || "";
const message = getArg("message") || "";
const urgent = hasFlag("urgent");
const successed = hasFlag("successed");
const priority = urgent ? "5" : "3";
const tags = successed ? "white_check_mark" : "x";

if (!message) {
  console.error("Error: --message is required");
  process.exit(1);
}

async function sendNtfy() {
  // Split NTFY_URL into root URL and topic
  // e.g. "https://ntfy.sh/my-topic" -> root="https://ntfy.sh", topic="my-topic"
  const parsed = new URL(process.env.NTFY_URL);
  const topic = parsed.pathname.slice(1);
  parsed.pathname = "/";

  const headers = { "Content-Type": "application/json; charset=utf-8" };
  if (process.env.NTFY_TOKEN) {
    headers["Authorization"] = `Bearer ${process.env.NTFY_TOKEN}`;
  }

  const body = JSON.stringify({
    topic,
    title,
    message,
    priority: Number(priority),
    tags: [tags],
  });

  const res = await fetch(parsed.toString(), { method: "POST", headers, body });
  console.log(res.status);
  if (!res.ok) {
    console.error(await res.text());
    process.exit(1);
  }
}

async function sendBark() {
  const body = JSON.stringify({
    title,
    body: message,
    group: "claude-code",
    level: priority === "5" ? "timeSensitive" : "active",
    icon: "https://claude.ai/favicon.ico",
  });

  const res = await fetch(process.env.BARK_URL, {
    method: "POST",
    headers: { "Content-Type": "application/json; charset=utf-8" },
    body,
  });
  console.log(res.status);
  if (!res.ok) {
    console.error(await res.text());
    process.exit(1);
  }
}

// Send to all configured providers
const results = await Promise.allSettled(
  providers.map((p) => (p === "ntfy" ? sendNtfy() : sendBark()))
);

const failures = results.filter((r) => r.status === "rejected");
if (failures.length > 0) {
  for (const f of failures) console.error(f.reason);
  process.exit(1);
}
