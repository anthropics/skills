#!/usr/bin/env node

const { readFileSync, writeFileSync, unlinkSync, mkdirSync } = require("fs");
const { join } = require("path");
const { homedir } = require("os");
const { execSync } = require("child_process");

const SCREENSHOT_PATH = join(homedir(), ".snap", "latest.png").replace(/\//g, "\\");

function countdownAndSnap(outputPath) {
  // One PowerShell script handles the whole experience:
  // balloon notification + beep countdown + screenshot
  const ps = `
Add-Type -AssemblyName System.Windows.Forms
Add-Type -AssemblyName System.Drawing

# Balloon notification — visible even when alt-tabbed to another window
$notify = New-Object System.Windows.Forms.NotifyIcon
$notify.Icon = [System.Drawing.SystemIcons]::Information
$notify.BalloonTipTitle = "snap:"
$notify.BalloonTipText = "Say cheese! Snapping in 3..."
$notify.Visible = $true
$notify.ShowBalloonTip(3500)

# Pleasant countdown — three dings, one per second
$ding = New-Object System.Media.SoundPlayer("$env:SystemRoot\\Media\\ding.wav")
$ding.PlaySync(); Start-Sleep -Milliseconds 750
$ding.PlaySync(); Start-Sleep -Milliseconds 750
$ding.PlaySync(); Start-Sleep -Milliseconds 750

# Snap! — chimes signal the capture moment
$chimes = New-Object System.Media.SoundPlayer("$env:SystemRoot\\Media\\chimes.wav")
$chimes.PlaySync()

# Take the screenshot
$screen = [System.Windows.Forms.Screen]::PrimaryScreen.Bounds
$bmp = New-Object System.Drawing.Bitmap($screen.Width, $screen.Height)
$g = [System.Drawing.Graphics]::FromImage($bmp)
$g.CopyFromScreen($screen.Location, [System.Drawing.Point]::Empty, $screen.Size)
$bmp.Save('${outputPath}', [System.Drawing.Imaging.ImageFormat]::Png)
$g.Dispose()
$bmp.Dispose()

$notify.Visible = $false
$notify.Dispose()
`.trim();

  const ps1path = join(homedir(), ".snap", "snap.ps1").replace(/\//g, "\\");
  writeFileSync(ps1path, ps);
  execSync(`powershell -NoProfile -ExecutionPolicy Bypass -WindowStyle Hidden -File "${ps1path}"`);
}

async function run() {
  const raw = readFileSync(0, "utf8");
  const input = JSON.parse(raw);
  const prompt = input.prompt ?? "";

  if (!prompt.trimStart().toLowerCase().startsWith("snap:")) {
    process.exit(0);
  }

  mkdirSync(require("path").dirname(SCREENSHOT_PATH), { recursive: true });
  try { unlinkSync(SCREENSHOT_PATH); } catch {}

  try {
    countdownAndSnap(SCREENSHOT_PATH);
  } catch (err) {
    process.exit(0);
  }

  const context = `Screenshot saved at ${SCREENSHOT_PATH}. Read this image file before responding.`;

  process.stdout.write(JSON.stringify({
    hookSpecificOutput: {
      hookEventName: "UserPromptSubmit",
      additionalContext: context
    }
  }));

  process.exit(0);
}

run();
