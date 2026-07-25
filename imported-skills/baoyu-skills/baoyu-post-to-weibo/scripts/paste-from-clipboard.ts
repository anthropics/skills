import { spawnSync } from 'node:child_process';
import process from 'node:process';

function printUsage(exitCode = 0): never {
  console.log(`Send real paste keystroke (Cmd+V / Ctrl+V) to the frontmost application

This bypasses CDP's synthetic events which websites can detect and ignore.

Usage:
  npx -y bun paste-from-clipboard.ts [options]

Options:
  --retries <n>     Number of retry attempts (default: 3)
  --delay <ms>      Delay between retries in ms (default: 500)
  --app <name>      Target application to activate first (macOS only)
  --help            Show this help

Examples:
  # Simple paste
  npx -y bun paste-from-clipboard.ts

  # Paste to Chrome with retries
  npx -y bun paste-from-clipboard.ts --app "Google Chrome" --retries 5

  # Quick paste with shorter delay
  npx -y bun paste-from-clipboard.ts --delay 200
`);
  process.exit(exitCode);
}

function sleepSync(ms: number): void {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);
}

function activateApp(appName: string): boolean {
  if (process.platform !== 'darwin') return false;

  // Activate and wait for app to be frontmost
  const script = `
    tell application "${appName}"
      activate
      delay 0.5
    end tell

    -- Verify app is frontmost
    tell application "System Events"
      set frontApp to name of first application process whose frontmost is true
      if frontApp is not "${appName}" then
        tell application "${appName}" to activate
        delay 0.3
      end if
    end tell
  `;
  const result = spawnSync('osascript', ['-e', script], { stdio: 'pipe' });
  return result.status === 0;
}

function pasteMac(retries: number, delayMs: number, targetApp?: string): boolean {
  for (let i = 0; i < retries; i++) {
    // Build script that activates app (if specified) and sends keystroke in one atomic operation
    const script = targetApp
      ? `
        tell application "${targetApp}"
          activate
        end tell
        delay 0.3
        tell application "System Events"
          keystroke "v" using command down
        end tell
      `
      : `
        tell application "System Events"
          keystroke "v" using command down
        end tell
      `;

    const result = spawnSync('osascript', ['-e', script], { stdio: 'pipe' });
    if (result.status === 0) {
      return true;
    }

    const stderr = result.stderr?.toString().trim();
    if (stderr) {
      console.error(`[paste] osascript error: ${stderr}`);
    }

    if (i < retries - 1) {
      console.error(`[paste] Attempt ${i + 1}/${retries} failed, retrying in ${delayMs}ms...`);
      sleepSync(delayMs);
    }
  }
  return false;
}

function pasteLinux(retries: number, delayMs: number): boolean {
  // Try xdotool first (X11), then ydotool (Wayland)
  const tools = [
    { cmd: 'xdotool', args: ['key', 'ctrl+v'] },
    { cmd: 'ydotool', args: ['key', '29:1', '47:1', '47:0', '29:0'] }, // Ctrl down, V down, V up, Ctrl up
  ];

  for (const tool of tools) {
    const which = spawnSync('which', [tool.cmd], { stdio: 'pipe' });
    if (which.status !== 0) continue;

    for (let i = 0; i < retries; i++) {
      const result = spawnSync(tool.cmd, tool.args, { stdio: 'pipe' });
      if (result.status === 0) {
        return true;
      }
      if (i < retries - 1) {
        console.error(`[paste] Attempt ${i + 1}/${retries} failed, retrying in ${delayMs}ms...`);
        sleepSync(delayMs);
      }
    }
    return false;
  }

  console.error('[paste] No supported tool found. Install xdotool (X11) or ydotool (Wayland).');
  return false;
}

function pasteWindows(retries: number, delayMs: number): boolean {
  const ps = `
    Add-Type -AssemblyName System.Windows.Forms
    [System.Windows.Forms.SendKeys]::SendWait("^v")
  `;

  for (let i = 0; i < retries; i++) {
    const result = spawnSync('powershell.exe', ['-NoProfile', '-Command', ps], { stdio: 'pipe' });
    if (result.status === 0) {
      return true;
    }
    if (i < retries - 1) {
      console.error(`[paste] Attempt ${i + 1}/${retries} failed, retrying in ${delayMs}ms...`);
      sleepSync(delayMs);
    }
  }
  return false;
}

function paste(retries: number, delayMs: number, targetApp?: string): boolean {
  switch (process.platform) {
    case 'darwin':
      return pasteMac(retries, delayMs, targetApp);
    case 'linux':
      return pasteLinux(retries, delayMs);
    case 'win32':
      return pasteWindows(retries, delayMs);
    default:
      console.error(`[paste] Unsupported platform: ${process.platform}`);
      return false;
  }
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);

  let retries = 3;
  let delayMs = 500;
  let targetApp: string | undefined;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i] ?? '';
    if (arg === '--help' || arg === '-h') {
      printUsage(0);
    }
    if (arg === '--retries' && args[i + 1]) {
      retries = parseInt(args[++i]!, 10) || 3;
    } else if (arg === '--delay' && args[i + 1]) {
      delayMs = parseInt(args[++i]!, 10) || 500;
    } else if (arg === '--app' && args[i + 1]) {
      targetApp = args[++i];
    } else if (arg.startsWith('-')) {
      console.error(`Unknown option: ${arg}`);
      printUsage(1);
    }
  }

  if (targetApp) {
    console.log(`[paste] Target app: ${targetApp}`);
  }
  console.log(`[paste] Sending paste keystroke (retries=${retries}, delay=${delayMs}ms)...`);
  const success = paste(retries, delayMs, targetApp);

  if (success) {
    console.log('[paste] Paste keystroke sent successfully');
  } else {
    console.error('[paste] Failed to send paste keystroke');
    process.exit(1);
  }
}

await main();
