import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { findChromeExecutable, getDefaultProfileDir } from './cdp.ts';

interface CheckResult {
  name: string;
  ok: boolean;
  detail: string;
}

const results: CheckResult[] = [];

function log(label: string, ok: boolean, detail: string): void {
  results.push({ name: label, ok, detail });
  const icon = ok ? '✅' : '❌';
  console.log(`${icon} ${label}: ${detail}`);
}

function warn(label: string, detail: string): void {
  results.push({ name: label, ok: true, detail });
  console.log(`⚠️  ${label}: ${detail}`);
}

async function checkChrome(): Promise<void> {
  const chromePath = findChromeExecutable();
  if (chromePath) {
    log('Chrome', true, chromePath);
  } else {
    log('Chrome', false, 'Not found. Set WECHAT_BROWSER_CHROME_PATH env var or install Chrome.');
  }
}

async function checkProfileIsolation(): Promise<void> {
  const profileDir = getDefaultProfileDir();
  const userChromeDir = process.platform === 'darwin'
    ? path.join(os.homedir(), 'Library', 'Application Support', 'Google', 'Chrome')
    : process.platform === 'win32'
      ? path.join(os.homedir(), 'AppData', 'Local', 'Google', 'Chrome', 'User Data')
      : path.join(os.homedir(), '.config', 'google-chrome');

  const isIsolated = !profileDir.startsWith(userChromeDir);
  log('Profile isolation', isIsolated, `Skill profile: ${profileDir}`);

  if (isIsolated) {
    const exists = fs.existsSync(profileDir);
    if (exists) {
      log('Profile dir', true, 'Exists and accessible');
    } else {
      try {
        fs.mkdirSync(profileDir, { recursive: true });
        log('Profile dir', true, 'Created successfully');
      } catch (e) {
        log('Profile dir', false, `Cannot create: ${e instanceof Error ? e.message : String(e)}`);
      }
    }
  }
}

async function checkAccessibility(): Promise<void> {
  if (process.platform !== 'darwin') {
    log('Accessibility', true, `Skipped (not macOS, platform: ${process.platform})`);
    return;
  }

  const result = spawnSync('osascript', ['-e', `
    tell application "System Events"
      set frontApp to name of first application process whose frontmost is true
      return frontApp
    end tell
  `], { stdio: 'pipe', timeout: 10_000 });

  if (result.status === 0) {
    const app = result.stdout?.toString().trim();
    log('Accessibility (System Events)', true, `Frontmost app: ${app}`);
  } else {
    const stderr = result.stderr?.toString().trim() || '';
    if (stderr.includes('not allowed assistive access') || stderr.includes('1002')) {
      log('Accessibility (System Events)', false,
        'Denied. Grant access: System Settings → Privacy & Security → Accessibility → enable your terminal app');
    } else {
      log('Accessibility (System Events)', false, `Failed: ${stderr}`);
    }
  }
}

async function checkClipboardCopy(): Promise<void> {
  if (process.platform !== 'darwin') {
    log('Clipboard copy (image)', true, `Skipped (not macOS)`);
    return;
  }

  const tmpDir = await mkdtemp(path.join(os.tmpdir(), 'wechat-check-'));
  try {
    const testPng = path.join(tmpDir, 'test.png');
    const swiftSrc = `import AppKit
import Foundation
let size = NSSize(width: 2, height: 2)
let image = NSImage(size: size)
image.lockFocus()
NSColor.red.set()
NSBezierPath.fill(NSRect(origin: .zero, size: size))
image.unlockFocus()
guard let tiff = image.tiffRepresentation,
      let rep = NSBitmapImageRep(data: tiff),
      let png = rep.representation(using: .png, properties: [:]) else {
  FileHandle.standardError.write("Failed to create test PNG\\n".data(using: .utf8)!)
  exit(1)
}
try png.write(to: URL(fileURLWithPath: CommandLine.arguments[1]))
`;
    const genScript = path.join(tmpDir, 'gen.swift');
    await writeFile(genScript, swiftSrc, 'utf8');
    const genResult = spawnSync('swift', [genScript, testPng], { stdio: 'pipe', timeout: 30_000 });
    if (genResult.status !== 0) {
      log('Clipboard copy (image)', false, `Cannot create test image: ${genResult.stderr?.toString().trim()}`);
      return;
    }

    const clipSrc = `import AppKit
import Foundation
guard let image = NSImage(contentsOfFile: CommandLine.arguments[1]) else {
  FileHandle.standardError.write("Failed to load image\\n".data(using: .utf8)!)
  exit(1)
}
let pb = NSPasteboard.general
pb.clearContents()
if !pb.writeObjects([image]) {
  FileHandle.standardError.write("Failed to write to clipboard\\n".data(using: .utf8)!)
  exit(1)
}
`;
    const clipScript = path.join(tmpDir, 'clip.swift');
    await writeFile(clipScript, clipSrc, 'utf8');
    const clipResult = spawnSync('swift', [clipScript, testPng], { stdio: 'pipe', timeout: 30_000 });
    if (clipResult.status === 0) {
      log('Clipboard copy (image)', true, 'Can copy image to clipboard via Swift/AppKit');
    } else {
      log('Clipboard copy (image)', false, `Failed: ${clipResult.stderr?.toString().trim()}`);
    }
  } finally {
    await rm(tmpDir, { recursive: true, force: true });
  }
}

async function checkPasteKeystroke(): Promise<void> {
  if (process.platform === 'darwin') {
    const result = spawnSync('osascript', ['-e', `
      tell application "System Events"
        set canSend to true
        return canSend
      end tell
    `], { stdio: 'pipe', timeout: 10_000 });

    if (result.status === 0) {
      log('Paste keystroke (osascript)', true, 'System Events can send keystrokes');
    } else {
      const stderr = result.stderr?.toString().trim() || '';
      log('Paste keystroke (osascript)', false, `Cannot send keystrokes: ${stderr}`);
    }
  } else if (process.platform === 'linux') {
    const xdotool = spawnSync('which', ['xdotool'], { stdio: 'pipe' });
    const ydotool = spawnSync('which', ['ydotool'], { stdio: 'pipe' });
    if (xdotool.status === 0) {
      log('Paste keystroke', true, 'xdotool available (X11)');
    } else if (ydotool.status === 0) {
      log('Paste keystroke', true, 'ydotool available (Wayland)');
    } else {
      log('Paste keystroke', false, 'No tool found. Install xdotool (X11) or ydotool (Wayland).');
    }
  } else if (process.platform === 'win32') {
    log('Paste keystroke', true, 'Windows uses PowerShell SendKeys (built-in)');
  }
}

async function checkBun(): Promise<void> {
  const result = spawnSync('npx', ['-y', 'bun', '--version'], { stdio: 'pipe', timeout: 30_000 });
  if (result.status === 0) {
    log('Bun runtime', true, `v${result.stdout?.toString().trim()}`);
  } else {
    log('Bun runtime', false, 'Cannot run bun. Install: brew install oven-sh/bun/bun (macOS) or npm install -g bun');
  }
}

async function checkApiCredentials(): Promise<void> {
  const cwd = process.cwd();
  const projectEnv = path.join(cwd, '.baoyu-skills', '.env');
  const userEnv = path.join(os.homedir(), '.baoyu-skills', '.env');

  let found = false;
  for (const envPath of [projectEnv, userEnv]) {
    if (fs.existsSync(envPath)) {
      const content = fs.readFileSync(envPath, 'utf8');
      if (content.includes('WECHAT_APP_ID')) {
        log('API credentials', true, `Found in ${envPath}`);
        found = true;
        break;
      }
    }
  }

  if (!found) {
    warn('API credentials', 'Not found. Required for API publishing method. Run the skill to set up via guided flow.');
  }
}

async function checkRunningChromeConflict(): Promise<void> {
  if (process.platform !== 'darwin') return;

  const result = spawnSync('pgrep', ['-f', 'Google Chrome'], { stdio: 'pipe' });
  const pids = result.stdout?.toString().trim().split('\n').filter(Boolean) || [];

  if (pids.length > 0) {
    warn('Running Chrome instances', `${pids.length} Chrome process(es) detected. The skill uses --user-data-dir for isolation, so this is safe.`);
  } else {
    log('Running Chrome instances', true, 'No existing Chrome processes');
  }
}

async function main(): Promise<void> {
  console.log('=== baoyu-post-to-wechat: Permission & Environment Check ===\n');

  await checkChrome();
  await checkProfileIsolation();
  await checkBun();
  await checkAccessibility();
  await checkClipboardCopy();
  await checkPasteKeystroke();
  await checkApiCredentials();
  await checkRunningChromeConflict();

  console.log('\n--- Summary ---');
  const failed = results.filter((r) => !r.ok);
  if (failed.length === 0) {
    console.log('All checks passed. Ready to post to WeChat.');
  } else {
    console.log(`${failed.length} issue(s) found:`);
    for (const f of failed) {
      console.log(`  ❌ ${f.name}: ${f.detail}`);
    }
    process.exit(1);
  }
}

await main().catch((err) => {
  console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});
