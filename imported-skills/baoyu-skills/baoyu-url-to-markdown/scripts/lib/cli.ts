#!/usr/bin/env bun

import {
  runConvertCommand,
  type ConvertCommandOptions,
  type OutputFormat,
  type WaitMode,
} from "./commands/convert";

export const HELP_TEXT = `
baoyu-fetch - Read a URL into Markdown or JSON with Chrome CDP

Usage:
  baoyu-fetch <url> [options]

Options:
  --output <file>       Save output to file
  --format <type>       Output format: markdown | json
  --json                Alias for --format json
  --adapter <name>      Force an adapter (e.g. x, generic)
  --download-media      Download adapter-reported media into ./imgs and ./videos, then rewrite markdown links
  --media-dir <dir>     Base directory for downloaded media. Defaults to the output directory
  --debug-dir <dir>     Write debug artifacts
  --cdp-url <url>       Reuse an existing Chrome DevTools endpoint
  --browser-path <path> Explicit Chrome binary path
  --chrome-profile-dir <path>
                        Chrome user data dir. Defaults to BAOYU_CHROME_PROFILE_DIR
                        or baoyu-skills/chrome-profile.
  --headless            Launch a temporary headless Chrome if needed
  --wait-for <mode>     Wait mode: interaction | force
                        interaction: start visible Chrome and auto-wait only when login or verification is required
                        force: start visible Chrome, then auto-continue after it detects login/challenge progress
                               or continue immediately when you press Enter
  --wait-for-interaction
                        Alias for --wait-for interaction
  --wait-for-login      Alias for --wait-for interaction
  --interaction-timeout <ms>
                        How long to wait for manual interaction before failing (default: 600000)
  --interaction-poll-interval <ms>
                        How often to poll interaction state while waiting (default: 1500)
  --login-timeout <ms>  Alias for --interaction-timeout
  --login-poll-interval <ms>
                        Alias for --interaction-poll-interval
  --timeout <ms>        Page timeout in milliseconds (default: 30000)
  --help                Show help

Examples:
  baoyu-fetch https://example.com
  baoyu-fetch https://example.com --format markdown --output article.md --download-media
  baoyu-fetch https://example.com --format json --output article.json
  baoyu-fetch https://x.com/lennysan/status/2036483059407810640 --wait-for interaction
  baoyu-fetch https://x.com/lennysan/status/2036483059407810640 --wait-for force
`.trim();

interface CliOptions extends ConvertCommandOptions {
  url?: string;
  help: boolean;
}

function normalizeWaitMode(raw: string): WaitMode {
  const value = raw.toLowerCase();
  if (value === "interaction" || value === "auto") {
    return "interaction";
  }
  if (value === "force" || value === "manual" || value === "always") {
    return "force";
  }
  throw new Error(`Invalid wait mode: ${raw}. Expected interaction or force.`);
}

function normalizeOutputFormat(raw: string): OutputFormat {
  const value = raw.toLowerCase();
  if (value === "markdown" || value === "json") {
    return value;
  }

  throw new Error(`Invalid output format: ${raw}. Expected markdown or json.`);
}

export function parseArgs(argv: string[]): CliOptions {
  const options: CliOptions = {
    format: "markdown",
    headless: false,
    downloadMedia: false,
    waitMode: "none",
    interactionTimeoutMs: 600_000,
    interactionPollIntervalMs: 1_500,
    timeoutMs: 30_000,
    help: false,
  };

  const args = argv.slice(2);
  for (let index = 0; index < args.length; index += 1) {
    const value = args[index];

    if (value === "--help" || value === "-h") {
      options.help = true;
      continue;
    }
    if (value === "--format") {
      const format = args[index + 1];
      if (!format) {
        throw new Error("--format requires a value");
      }
      options.format = normalizeOutputFormat(format);
      index += 1;
      continue;
    }
    if (value === "--json") {
      options.format = "json";
      continue;
    }
    if (value === "--download-media") {
      options.downloadMedia = true;
      continue;
    }
    if (value === "--headless") {
      options.headless = true;
      continue;
    }
    if (value === "--wait-for") {
      const mode = args[index + 1];
      if (!mode) {
        throw new Error("--wait-for requires a mode");
      }
      options.waitMode = normalizeWaitMode(mode);
      index += 1;
      continue;
    }
    if (value === "--wait-for-interaction" || value === "--wait-for-login") {
      options.waitMode = "interaction";
      continue;
    }
    if (value === "--output") {
      options.output = args[index + 1];
      index += 1;
      continue;
    }
    if (value === "--adapter") {
      options.adapter = args[index + 1];
      index += 1;
      continue;
    }
    if (value === "--debug-dir") {
      options.debugDir = args[index + 1];
      index += 1;
      continue;
    }
    if (value === "--media-dir") {
      options.mediaDir = args[index + 1];
      index += 1;
      continue;
    }
    if (value === "--cdp-url") {
      options.cdpUrl = args[index + 1];
      index += 1;
      continue;
    }
    if (value === "--browser-path") {
      options.browserPath = args[index + 1];
      index += 1;
      continue;
    }
    if (value === "--chrome-profile-dir") {
      options.chromeProfileDir = args[index + 1];
      index += 1;
      continue;
    }
    if (value === "--timeout") {
      const parsed = Number(args[index + 1]);
      if (!Number.isFinite(parsed) || parsed <= 0) {
        throw new Error(`Invalid timeout: ${args[index + 1]}`);
      }
      options.timeoutMs = parsed;
      index += 1;
      continue;
    }
    if (value === "--interaction-timeout" || value === "--login-timeout") {
      const parsed = Number(args[index + 1]);
      if (!Number.isFinite(parsed) || parsed <= 0) {
        throw new Error(`Invalid interaction timeout: ${args[index + 1]}`);
      }
      options.interactionTimeoutMs = parsed;
      index += 1;
      continue;
    }
    if (value === "--interaction-poll-interval" || value === "--login-poll-interval") {
      const parsed = Number(args[index + 1]);
      if (!Number.isFinite(parsed) || parsed <= 0) {
        throw new Error(`Invalid interaction poll interval: ${args[index + 1]}`);
      }
      options.interactionPollIntervalMs = parsed;
      index += 1;
      continue;
    }
    if (value.startsWith("-")) {
      throw new Error(`Unknown option: ${value}`);
    }
    if (!options.url) {
      options.url = value;
      continue;
    }
    throw new Error(`Unexpected argument: ${value}`);
  }

  return options;
}

async function main(): Promise<void> {
  try {
    const options = parseArgs(process.argv);
    if (options.help || !options.url) {
      console.log(HELP_TEXT);
      return;
    }

    await runConvertCommand(options);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.error(message);
    process.exitCode = 1;
  }
}

if (import.meta.main) {
  void main();
}
