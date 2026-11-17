# Agent Notify - Windows Notification Script
# Plays system sound and flashes taskbar icon
param(
    [string]$Type = "default",
    [string]$ConfigPath = ""
)

# Load config if provided
$config = $null
if ($ConfigPath -and (Test-Path $ConfigPath)) {
    $config = Get-Content $ConfigPath -Raw | ConvertFrom-Json
}

# Get flash count from config or use default
$flashCount = 5
if ($config -and $config.taskbar -and $null -ne $config.taskbar.flashCount) {
    $flashCount = [int]$config.taskbar.flashCount
}

# Get custom sound path from config
$customSound = $null
if ($config -and $config.sounds -and $config.sounds.$Type) {
    $customSound = $config.sounds.$Type
}

# Add FlashWindow API
Add-Type @"
using System;
using System.Runtime.InteropServices;

public class FlashWindow {
    [StructLayout(LayoutKind.Sequential)]
    public struct FLASHWINFO {
        public UInt32 cbSize;
        public IntPtr hwnd;
        public UInt32 dwFlags;
        public UInt32 uCount;
        public UInt32 dwTimeout;
    }

    [DllImport("user32.dll")]
    [return: MarshalAs(UnmanagedType.Bool)]
    public static extern bool FlashWindowEx(ref FLASHWINFO pwfi);

    [DllImport("user32.dll")]
    public static extern IntPtr GetForegroundWindow();

    public const UInt32 FLASHW_ALL = 3;
    public const UInt32 FLASHW_TIMERNOFG = 12;

    public static void Flash(IntPtr hwnd, UInt32 count) {
        FLASHWINFO fw = new FLASHWINFO();
        fw.cbSize = Convert.ToUInt32(Marshal.SizeOf(fw));
        fw.hwnd = hwnd;
        fw.dwFlags = FLASHW_ALL | FLASHW_TIMERNOFG;
        fw.uCount = count;
        fw.dwTimeout = 0;
        FlashWindowEx(ref fw);
    }
}
"@ -ErrorAction SilentlyContinue

# Play sound
if ($customSound -and (Test-Path $customSound)) {
    # Play custom sound file
    $player = New-Object System.Media.SoundPlayer
    $player.SoundLocation = $customSound
    $player.Play()
} else {
    # Play system sound based on type
    switch ($Type) {
        "confirm" {
            [System.Media.SystemSounds]::Exclamation.Play()
        }
        "done" {
            [System.Media.SystemSounds]::Asterisk.Play()
        }
        "error" {
            [System.Media.SystemSounds]::Hand.Play()
        }
        default {
            [System.Media.SystemSounds]::Beep.Play()
        }
    }
}

# Flash taskbar for terminal windows
$terminalProcesses = @('WindowsTerminal', 'cmd', 'powershell', 'pwsh', 'Code', 'claude')
$procs = Get-Process | Where-Object {
    $_.MainWindowHandle -ne 0 -and ($terminalProcesses -contains $_.ProcessName)
}
foreach ($proc in $procs) {
    [FlashWindow]::Flash($proc.MainWindowHandle, $flashCount)
}
