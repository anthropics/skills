---
name: sensory
description: >
  Native macOS automation via AppleScript — 50x faster than screenshot-based computer use.
  Use this skill ANY time you interact with the user's Mac: clicking buttons, reading screen
  content, typing text, navigating menus, filling forms, managing windows, switching apps,
  keyboard shortcuts, opening files, handling dialogs, Spotlight search, system settings,
  or ANY GUI interaction. MUST be your first choice over computer-use tools. Trigger on:
  controlling apps, clicking, typing, reading screen, opening/closing/switching apps, Finder,
  system settings, "open", "type", "check", "read", "find", "close", "minimize", "search",
  or ANY request involving the user's macOS desktop.
---

# Sensory: Native macOS Automation for Claude

You have access to `mcp__Control_your_Mac__osascript`, a tool that executes AppleScript directly on the user's Mac. This is your primary interface to macOS — it talks to apps through Apple's Accessibility API, which means you interact with UI elements by their actual identity (name, role, position in the hierarchy) rather than guessing pixel coordinates from screenshots.

This approach is inspired by the DockWright macOS agent architecture, which demonstrated that direct Accessibility API interaction is fundamentally faster and more reliable than vision-based screen automation.

## Why This Replaces Computer Use

The screenshot approach works like this: capture the screen (slow) → analyze the image with vision (slow) → guess which pixel to click (error-prone) → click and hope → screenshot again to verify (slow again). That's 5-15 seconds per action, and it often misses.

osascript works like this: tell the app what to do by name → done. One call, sub-second, no guessing.

**Always use osascript.** The only times computer use might still be needed: apps with zero accessibility support (very rare), or when you need to visually interpret complex graphics/images. For everything else — osascript wins.

## Two Tiers of Access (IMPORTANT)

Not all AppleScript features require the same permissions. Understanding this is critical because many users won't have Accessibility permissions enabled.
### Tier 1: Works Out of the Box (No Special Permissions)

These use each app's built-in AppleScript dictionary — talking directly to the app, not through System Events UI control. This is your **default approach**. Always try Tier 1 first.

- **Direct app scripting:** `tell application "Safari" to get URL of current tab of window 1`
- **Finder operations:** list files, move, trash, open, create folders, get file info
- **Safari/Chrome:** open tabs, get URLs, get page titles, read page text, run JavaScript
- **Mail:** read unread count, get subjects, compose emails, search messages
- **Notes:** create, read, delete, search notes
- **TextEdit:** create documents, set/get text
- **Calendar:** list events, create events
- **Spotify:** play, pause, next, get track info
- **Spotlight search:** `do shell script "mdfind -name 'filename'"`
- **Shell commands:** `do shell script "any unix command"`
- **Volume control:** `set volume output volume 50`
- **Dark mode:** `tell application "System Events" to tell appearance preferences to set dark mode to true`
- **Clipboard:** `set the clipboard to "text"` / `the clipboard`
- **Notifications:** `display notification "msg" with title "title"`
- **Open URLs:** `open location "https://example.com"`
- **Open files:** `do shell script "open '/path/to/file'"`
- **Window management via app API:** `set bounds of window 1 to {x, y, w, h}` (through the app itself)
- **Battery, Wi-Fi, system info:** via `do shell script` with `pmset`, `networksetup`, etc.

### Tier 2: Requires Accessibility Permissions (System Events UI Control)

These use `tell application "System Events" to tell process "AppName"` to interact with UI elements. They require the user to grant Accessibility access in System Settings → Privacy & Security → Accessibility.

- **Keystroke simulation:** `keystroke "text"`, `key code 36`
- **Clicking buttons/checkboxes:** `click button "Save" of window 1`- **Reading UI elements:** `get value of text field 1 of window 1`
- **Menu bar navigation:** `click menu item "New" of menu "File" of menu bar 1`
- **Form filling via UI:** `set value of text field 1 to "text"` (through System Events)
- **UI element discovery:** `get every UI element of window 1`

**If a Tier 2 command fails with an error like "not allowed assistive access" or "no permission to send keystrokes":**

1. First, try to accomplish the same task using Tier 1 (direct app API). Often you can — for example, instead of typing into Notes via keystroke, use `make new note with properties`.
2. If Tier 2 is truly needed, guide the user to enable permissions:

```applescript
do shell script "open 'x-apple.systempreferences:com.apple.preference.security?Privacy_Accessibility'"
```

Tell them: "To click buttons and type in apps, you need to grant Accessibility access. I've opened the right Settings page — add [the app running Claude] to the allowed list. This is a one-time setup."

### Decision Flow

When you need to interact with an app, think in this order:
1. **Can the app's own AppleScript dictionary do this?** (Tier 1 — always try first)
2. **Can a shell command do this?** (Tier 1 — `do shell script`)
3. **Do I need to click/type in the UI?** (Tier 2 — may need permissions)

Most tasks can be done entirely in Tier 1. A user who never enables Accessibility permissions can still get enormous value from this skill.

## Core Principle: Identity Over Pixels

Every interaction follows the same philosophy — address things by what they are, not where they are on screen.

**Tier 1 (direct app API — preferred):**```applescript
-- Talk to the app directly
tell application "Safari"
    set URL of current tab of window 1 to "https://example.com"
end tell
```

**Tier 2 (System Events UI — when needed):**
```applescript
-- Talk to the UI elements through System Events
tell application "System Events" to tell process "Safari"
    click button "Reload" of toolbar 1 of window 1
end tell
```

Always try Tier 1 first. Use `tell application "AppName"` for direct app control. Use `tell application "System Events" to tell process "ProcessName"` only when you need to interact with UI elements that the app doesn't expose in its own dictionary.

## The Toolkit

### 1. Discover What's On Screen

Before acting on an unfamiliar app, discover what's available. This is like DockWright's ProcessSymbiosis — build a mental model before you act.

```applescript
-- What app is in front?
tell application "System Events"
    get name of first application process whose frontmost is true
end tell
-- What windows does it have?
tell application "System Events" to tell process "AppName"
    get name of every window
end tell

-- What's in the window? (buttons, fields, labels, etc.)
tell application "System Events" to tell process "AppName"
    get every UI element of window 1
end tell

-- Get details about all buttons
tell application "System Events" to tell process "AppName"
    get {name, description, enabled} of every button of window 1
end tell

-- Look deeper — what's inside a group or toolbar
tell application "System Events" to tell process "AppName"
    get every UI element of toolbar 1 of window 1
    get every UI element of group 1 of window 1
end tell

-- Nuclear option: get EVERYTHING (use sparingly — can be slow on complex windows)
tell application "System Events" to tell process "AppName"
    get entire contents of window 1
end tell
```

**When to discover vs. go direct:**
- **Go direct** when the action is obvious (click "Save", type Cmd+C, open an app)
- **Discover first** when you don't know the app's UI layout, or your first direct attempt fails
- **Always discover** when working with unfamiliar or complex apps (System Settings, custom enterprise apps)
### 2. Click Any UI Element

```applescript
-- Button by name
tell application "System Events" to tell process "AppName"
    click button "OK" of window 1
end tell

-- Button by index (when names aren't helpful)
tell application "System Events" to tell process "AppName"
    click button 2 of window 1
end tell

-- Checkbox
tell application "System Events" to tell process "AppName"
    click checkbox "Enable notifications" of window 1
end tell

-- Radio button
tell application "System Events" to tell process "AppName"
    click radio button "Option A" of radio group 1 of window 1
end tell

-- Tab
tell application "System Events" to tell process "AppName"
    click radio button "General" of tab group 1 of window 1
end tell
-- Dropdown (pop-up button) — two steps: click to open, then select
tell application "System Events" to tell process "AppName"
    click pop up button 1 of window 1
    delay 0.2
    click menu item "Choice B" of menu 1 of pop up button 1 of window 1
end tell

-- Table row
tell application "System Events" to tell process "AppName"
    select row 3 of table 1 of scroll area 1 of window 1
end tell

-- Link or any clickable static text
tell application "System Events" to tell process "AppName"
    click static text "Learn More" of group 1 of window 1
end tell

-- Element inside a sheet (modal dialog attached to window)
tell application "System Events" to tell process "AppName"
    click button "Don't Save" of sheet 1 of window 1
end tell

-- Element inside an alert dialog
tell application "System Events" to tell process "AppName"
    click button "OK" of dialog 1
end tell
```

### 3. Type Text and Fill Forms

```applescript-- Type into the currently focused element
tell application "System Events"
    keystroke "Hello, world!"
end tell

-- Set a field's value directly (faster — no typing animation)
tell application "System Events" to tell process "AppName"
    set value of text field 1 of window 1 to "Hello, world!"
end tell

-- Click a field first, then type
tell application "System Events" to tell process "AppName"
    click text field "Search" of toolbar 1 of window 1
    delay 0.1
    keystroke "query"
    keystroke return
end tell

-- Clear a field before typing
tell application "System Events" to tell process "AppName"
    click text field 1 of window 1
    keystroke "a" using command down  -- Select All
    keystroke "New text"
end tell

-- Set a text area (multi-line)
tell application "System Events" to tell process "AppName"
    set value of text area 1 of scroll area 1 of window 1 to "Line 1
Line 2
Line 3"
end tell
-- Tab between form fields
tell application "System Events"
    keystroke "First Name"
    keystroke tab
    keystroke "Last Name"
    keystroke tab
    keystroke "email@example.com"
    keystroke return  -- Submit
end tell

-- Fill forms with delays for reactive apps (web views, Electron apps)
tell application "System Events" to tell process "AppName"
    click text field 1 of window 1
    delay 0.1
    set value of text field 1 of window 1 to "username"
    delay 0.1
    click text field 2 of window 1
    delay 0.1
    set value of text field 2 of window 1 to "password"
    delay 0.1
    click button "Sign In" of window 1
end tell
```

### 4. Read Screen Content (No Screenshots Needed)

This is where Sensory truly shines — read text from any app instantly, without OCR.

```applescript
-- Window title
tell application "System Events" to tell process "AppName"
    get name of window 1
end tell
-- Text field content
tell application "System Events" to tell process "AppName"
    get value of text field 1 of window 1
end tell

-- All visible labels/text
tell application "System Events" to tell process "AppName"
    get value of every static text of window 1
end tell

-- Text area content
tell application "System Events" to tell process "AppName"
    get value of text area 1 of scroll area 1 of window 1
end tell

-- Checkbox state (0 = unchecked, 1 = checked)
tell application "System Events" to tell process "AppName"
    get value of checkbox "Auto-save" of window 1
end tell

-- Selected tab
tell application "System Events" to tell process "AppName"
    get value of tab group 1 of window 1
end tell
-- Dropdown current value
tell application "System Events" to tell process "AppName"
    get value of pop up button 1 of window 1
end tell

-- Read all text from every element (comprehensive screen read)
tell application "System Events" to tell process "AppName"
    set allText to {}
    repeat with elem in (every static text of window 1)
        try
            set end of allText to value of elem
        end try
    end repeat
    return allText
end tell

-- What element is focused right now
tell application "System Events"
    get description of first UI element whose focused is true
end tell
```

### 5. Keyboard Shortcuts

```applescript
-- Common shortcuts
tell application "System Events"
    keystroke "c" using command down          -- Copy
    keystroke "v" using command down          -- Paste
    keystroke "x" using command down          -- Cut
    keystroke "a" using command down          -- Select All    keystroke "s" using command down          -- Save
    keystroke "z" using command down          -- Undo
    keystroke "f" using command down          -- Find
    keystroke "w" using command down          -- Close window/tab
    keystroke "q" using command down          -- Quit app
    keystroke "n" using command down          -- New
    keystroke "t" using command down          -- New tab
    keystroke "p" using command down          -- Print
    keystroke "," using command down          -- Preferences/Settings
end tell

-- Multi-modifier
tell application "System Events"
    keystroke "s" using {command down, shift down}    -- Save As
    keystroke "z" using {command down, shift down}    -- Redo
    keystroke "3" using {command down, shift down}    -- Screenshot (full)
    keystroke "4" using {command down, shift down}    -- Screenshot (selection)
    keystroke "5" using {command down, shift down}    -- Screenshot toolbar
    keystroke "i" using {command down, option down}   -- Inspector/Dev Tools
    keystroke "q" using {command down, option down}   -- Force Quit dialog
end tell

-- Special keys by key code
tell application "System Events"
    key code 36                    -- Return/Enter
    key code 53                    -- Escape
    key code 48                    -- Tab
    key code 51                    -- Delete (backspace)
    key code 117                   -- Forward Delete
    key code 126                   -- Up arrow
    key code 125                   -- Down arrow    key code 123                   -- Left arrow
    key code 124                   -- Right arrow
    key code 49                    -- Space
    key code 121                   -- Page Down
    key code 116                   -- Page Up
    key code 115                   -- Home
    key code 119                   -- End
    key code 122                   -- F1
    key code 120                   -- F2
    key code 99                    -- F3 (Mission Control)
    key code 118                   -- F4 (Launchpad)
end tell
```

### 6. Menu Navigation

```applescript
-- Click a menu item
tell application "System Events" to tell process "AppName"
    click menu item "New Document" of menu "File" of menu bar 1
end tell

-- Submenu
tell application "System Events" to tell process "AppName"
    click menu item "PDF" of menu "Export As" of menu item "Export As" of menu "File" of menu bar 1
end tell

-- List all menus (discover what's available)
tell application "System Events" to tell process "AppName"
    get name of every menu bar item of menu bar 1
end tell

-- List items in a specific menu
tell application "System Events" to tell process "AppName"
    get name of every menu item of menu "File" of menu bar 1
end tell
```
### 7. File Dialogs (Save As, Open, Export)

File dialogs are one of the biggest pain points with computer use — they're complex, nested, and vary across apps. With osascript, they're straightforward.

```applescript
-- Navigate a Save dialog: type the filename and path
tell application "System Events" to tell process "AppName"
    -- The save dialog is usually a sheet on the window
    -- Type the filename
    set value of text field 1 of sheet 1 of window 1 to "my-document.pdf"

    -- If the dialog is in "compact" mode, expand it to see the file browser
    -- (the disclosure triangle or expand button)
    try
        click button 2 of sheet 1 of window 1  -- the expand button (varies)
    end try

    -- Navigate to a folder using Cmd+Shift+G (Go To Folder)
    keystroke "g" using {command down, shift down}
    delay 0.3
    keystroke "/Users/username/Documents/"
    delay 0.2
    keystroke return
    delay 0.3

    -- Click Save
    click button "Save" of sheet 1 of window 1
end tell
-- Handle Open dialogs similarly
tell application "System Events" to tell process "AppName"
    -- Cmd+Shift+G to type a path directly
    keystroke "g" using {command down, shift down}
    delay 0.3
    keystroke "/path/to/file.pdf"
    delay 0.2
    keystroke return
    delay 0.3
    click button "Open" of sheet 1 of window 1
end tell

-- Handle "Replace?" confirmation dialogs
tell application "System Events" to tell process "AppName"
    try
        click button "Replace" of sheet 1 of sheet 1 of window 1
    end try
end tell

-- Handle "Don't Save / Cancel / Save" dialogs
tell application "System Events" to tell process "AppName"
    try
        click button "Don't Save" of sheet 1 of window 1
    on error
        -- Some apps use a different dialog structure
        click button "Don't Save" of window 1
    end try
end tell
```
### 8. Spotlight Search (Fastest Way to Launch Anything)

```applescript
-- Open Spotlight
tell application "System Events"
    keystroke space using command down
    delay 0.3
end tell

-- Search and open
tell application "System Events"
    keystroke space using command down
    delay 0.3
    keystroke "Calculator"
    delay 0.5
    keystroke return
end tell

-- Open a file via Spotlight
tell application "System Events"
    keystroke space using command down
    delay 0.3
    keystroke "quarterly report"
    delay 0.8  -- give Spotlight time to index
    keystroke return
end tell
```

### 9. Window Management

```applescript-- Get window position and size
tell application "System Events" to tell process "AppName"
    get {position, size} of window 1
end tell

-- Move a window
tell application "System Events" to tell process "AppName"
    set position of window 1 to {100, 100}
end tell

-- Resize
tell application "System Events" to tell process "AppName"
    set size of window 1 to {1200, 800}
end tell

-- Minimize / restore
tell application "System Events" to tell process "AppName"
    set miniaturized of window 1 to true   -- minimize
    set miniaturized of window 1 to false  -- restore
end tell

-- List all windows
tell application "System Events" to tell process "AppName"
    get name of every window
end tell

-- Close a window
tell application "System Events" to tell process "AppName"
    click button 1 of window 1  -- red close button (usually index 1)
end tell

-- Bring a specific window to fronttell application "System Events" to tell process "AppName"
    perform action "AXRaise" of window "Document.txt"
end tell

-- Tile windows side by side (macOS Sequoia+)
-- Use keyboard shortcuts or manual positioning:
tell application "System Events" to tell process "AppName"
    set position of window 1 to {0, 25}
    set size of window 1 to {960, 1050}
end tell
```

### 10. App Management

```applescript
-- Launch an app
tell application "Safari" to activate

-- Launch by bundle ID (more reliable for some apps)
do shell script "open -b com.apple.Safari"

-- Open a specific file with an app
do shell script "open -a 'Visual Studio Code' '/path/to/project'"

-- Get all running apps
tell application "System Events"
    get name of every application process whose background only is falseend tell

-- Quit an app gracefully
tell application "Safari" to quit

-- Force quit
do shell script "killall Safari"

-- Hide an app
tell application "System Events" to set visible of process "Safari" to false

-- Show all windows of an app (un-hide)
tell application "System Events" to set visible of process "Safari" to true

-- Check if an app is running
tell application "System Events"
    set isRunning to exists (process "Safari")
    return isRunning
end tell
```

### 11. Scrolling

```applescript
-- Arrow key scrolling (works in most apps)
tell application "System Events"
    key code 125  -- down arrow
    key code 126  -- up arrow
end tell

-- Page down / Page uptell application "System Events"
    key code 121  -- page down
    key code 116  -- page up
end tell

-- Jump to top / bottom
tell application "System Events"
    keystroke "↑" using command down  -- top (Cmd+Up or Cmd+Home)
    keystroke "↓" using command down  -- bottom
end tell
-- Or use key codes:
tell application "System Events"
    key code 126 using command down  -- Cmd+Up = top
    key code 125 using command down  -- Cmd+Down = bottom
end tell
```

### 12. System Controls

```applescript
-- Volume
set volume output volume 50         -- 0-100
set volume with output muted        -- mute
set volume without output muted     -- unmute
get output volume of (get volume settings)

-- Dark mode
tell application "System Events" to tell appearance preferences
    set dark mode to not dark mode  -- toggle
    return dark mode as text
end tell
-- Clipboard
set the clipboard to "text to copy"
get the clipboard               -- read clipboard

-- Open a URL
open location "https://example.com"

-- Open a file
do shell script "open '/path/to/file.pdf'"

-- Open a folder in Finder
do shell script "open ~/Documents"

-- Take a screenshot (saves to Desktop)
do shell script "screencapture ~/Desktop/screenshot.png"

-- Screenshot a specific area (interactive)
do shell script "screencapture -i ~/Desktop/screenshot.png"

-- Screenshot without shadow
do shell script "screencapture -o ~/Desktop/screenshot.png"

-- Get battery status
do shell script "pmset -g batt | grep -o '[0-9]*%'"

-- Wi-Fi on/off
do shell script "networksetup -setairportpower en0 on"
do shell script "networksetup -setairportpower en0 off"
do shell script "networksetup -getairportpower en0"
-- Get current Wi-Fi network
do shell script "networksetup -getairportnetwork en0"

-- Bluetooth (requires blueutil if installed)
-- do shell script "blueutil --power 0"  -- off
-- do shell script "blueutil --power 1"  -- on

-- Lock screen
tell application "System Events" to keystroke "q" using {command down, control down}

-- Empty trash
tell application "Finder" to empty the trash

-- Notification
display notification "Task complete!" with title "Claude" sound name "Glass"

-- Show a dialog to the user
display dialog "Would you like to proceed?" buttons {"Cancel", "OK"} default button "OK"
```

### 13. Multi-App Workflows

Common pattern: read from one app, act in another.

```applescript
-- Copy text from one app and paste into another
tell application "TextEdit" to activate
delay 0.3
tell application "System Events"
    keystroke "a" using command down  -- Select all
    keystroke "c" using command down  -- Copyend tell
delay 0.2
tell application "Notes" to activate
delay 0.3
tell application "System Events"
    keystroke "n" using command down  -- New note
    delay 0.2
    keystroke "v" using command down  -- Paste
end tell

-- Read a value from one app, use it in another
tell application "System Events" to tell process "Calculator"
    set calcResult to value of static text 1 of group 1 of window 1
end tell
-- Now use calcResult in another context
```

### 14. Handling Alerts, Dialogs, and Sheets

macOS apps show three kinds of popups: alerts (floating dialogs), sheets (attached to window), and notifications.

```applescript
-- Handle a standard alert dialog
tell application "System Events" to tell process "AppName"
    -- Alerts might be a separate window or a dialog
    try        click button "OK" of window 1
    on error
        -- Try as a sheet
        click button "OK" of sheet 1 of window 1
    end try
end tell

-- Dismiss a "save changes?" dialog
tell application "System Events" to tell process "AppName"
    try
        click button "Don't Save" of sheet 1 of window 1
    on error
        try
            click button "Don't Save" of dialog 1
        on error
            click button "Don't Save" of window 1
        end try
    end try
end tell

-- Handle authentication dialogs (system-level)
tell application "System Events"
    try
        set value of text field 1 of window 1 of process "SecurityAgent" to "password"
        click button "OK" of window 1 of process "SecurityAgent"
    end try
end tell

-- Wait for a dialog to appear, then handle it
tell application "System Events" to tell process "AppName"    repeat 10 times
        try
            if exists sheet 1 of window 1 then
                click button "OK" of sheet 1 of window 1
                exit repeat
            end if
        end try
        delay 0.5
    end repeat
end tell
```

### 15. Dock and Mission Control

```applescript
-- Show all windows (Mission Control)
tell application "System Events"
    key code 126 using control down  -- Ctrl+Up = Mission Control
end tell

-- Show application windows
tell application "System Events"
    key code 125 using control down  -- Ctrl+Down = App Exposé
end tell

-- Show Desktop
tell application "System Events"
    key code 122 using command down  -- Cmd+F3 sometimes, or:
    -- key code 99  -- F3 for Mission Control (varies by keyboard settings)
end tell
-- Switch between desktops/spaces
tell application "System Events"
    key code 124 using control down  -- Ctrl+Right = next Space
    key code 123 using control down  -- Ctrl+Left = previous Space
end tell

-- Open Launchpad
tell application "System Events"
    key code 118  -- F4 if configured
end tell
-- Or more reliably:
do shell script "open -a Launchpad"
```

## Process Name Quirks

One of the biggest gotchas: the process name (what System Events calls the app) often differs from the app's display name. Here's how to find the correct process name:

```applescript
-- Find the process name of the frontmost app
tell application "System Events"
    get name of first application process whose frontmost is true
end tell
```

**Common mismatches:**
| App Name | Process Name |
|----------|-------------|
| Visual Studio Code | Code |
| Google Chrome | Google Chrome |
| Microsoft Word | Microsoft Word || Microsoft Excel | Microsoft Excel |
| System Settings | System Settings |
| Activity Monitor | Activity Monitor |
| App Store | App Store |
| 1Password | 1Password 7 (or 1Password) |

When in doubt, activate the app first and then query for the frontmost process name.

## Error Handling and Recovery

AppleScript errors are your friend — they tell you exactly what's wrong.

**Common errors and fixes:**

1. **"Can't get window 1"** → App has no windows open. Open one: `tell application "AppName" to activate` then `make new document`
2. **"Can't get button 'Save'"** → Element doesn't exist with that name. Discover: `get name of every button of window 1`
3. **"Process 'AppName' is not running"** → Launch it: `tell application "AppName" to activate`
4. **"Not allowed assistive access"** → Accessibility permissions needed (see setup section above)
5. **"Connection is invalid"** → App crashed or isn't responding. Try: `do shell script "killall AppName"` then relaunch
6. **Timeout** → App UI is slow to load. Add `delay 0.5` before the action

**Robust pattern with retry:**
```applescript
tell application "System Events" to tell process "AppName"
    set maxRetries to 3
    set attempts to 0
    repeat
        set attempts to attempts + 1
        try
            click button "Submit" of window 1
            exit repeat        on error errMsg
            if attempts ≥ maxRetries then
                error "Failed after " & maxRetries & " attempts: " & errMsg
            end if
            delay 0.5
        end try
    end repeat
end tell
```

## String Escaping

When building AppleScript with dynamic content, escape carefully:
- Backslashes: `\` → `\\`
- Double quotes: `"` → `\"`

This matters when the text you're typing or setting contains quotes or special characters.

## Performance Tips

- **Batch operations:** Combine multiple reads/actions in a single `tell` block — one osascript call is faster than three
- **`set value` over `keystroke`:** Setting a field value directly is faster than simulating typing
- **Skip `entire contents`** on complex windows — it traverses the whole UI tree and can be slow. Target specific areas
- **Use `delay` only when needed:** Some apps (especially Electron/web-based apps) need 0.1-0.3s delays between actions for the UI to catch up. Native apps rarely need delays
- **Cache process names:** If you'll interact with an app repeatedly, find its process name once and reuse it

## Shortcuts.app Integration

macOS Shortcuts can be triggered from AppleScript, giving you access to powerful pre-built automations and the ability to chain complex workflows.

```applescript
-- Run a Shortcut by name [Tier 1]
do shell script "shortcuts run 'My Shortcut Name'"

-- Run a Shortcut with input [Tier 1]
do shell script "echo 'input text' | shortcuts run 'Process Text'"

-- Run a Shortcut and capture output [Tier 1]
set result to do shell script "shortcuts run 'Get Weather' | cat"

-- List all available Shortcuts [Tier 1]
set allShortcuts to do shell script "shortcuts list"

-- Run a Shortcut with a file as input [Tier 1]
do shell script "shortcuts run 'Convert Image' -i '/path/to/image.png'"

-- Open Shortcuts app to a specific shortcut [Tier 1]
do shell script "open -a Shortcuts"
```

**Useful built-in Shortcut actions you can trigger:**
- Focus modes: `shortcuts run 'Set Focus'`
- Home automation: `shortcuts run 'Turn Off Lights'`
- File conversions: pipe files through Shortcuts
- Multi-step workflows: chain multiple app actions that would take several osascript calls

**Pro tip:** If a user has complex automation needs (e.g., "when I get an email from X, save the attachment to Y and notify me on Z"), suggest they create a Shortcut and trigger it via osascript. It's often cleaner than scripting each step individually.

## Drag and Drop

AppleScript can simulate drag-and-drop operations using click-and-drag actions via System Events. These are Tier 2 (require Accessibility permissions).

```applescript
-- Drag from one position to another (pixel coordinates)
tell application "System Events" to tell process "Finder"
    -- First, get the position of the source element
    set sourcePos to position of icon 1 of scroll area 1 of window 1
    set targetPos to position of icon 2 of scroll area 1 of window 1

    -- Drag uses click-hold-move-release pattern
    -- Note: AppleScript doesn't have a native drag command, use this workaround:
end tell

-- Alternative: Use the Finder's own move command instead of drag [Tier 1 — preferred]
tell application "Finder"
    move file "document.pdf" of desktop to folder "Projects" of home
end tell

-- For apps that need actual drag simulation, use cliclick (if installed) [Tier 1]
-- Install: brew install cliclick
do shell script "cliclick dd:100,200 du:300,400"
-- dd = drag down (mouse press), du = drag up (mouse release)

-- Reorder items in a list (e.g., drag row 3 above row 1) [Tier 2]
-- Most apps support keyboard-based reordering instead:
tell application "System Events" to tell process "Reminders"
    select row 3 of table 1 of scroll area 1 of window 1
    -- Use Cmd+Option+Up/Down if the app supports it
    key code 126 using {command down, option down}  -- move up
end tell
```

**Best practice:** Avoid pixel-based drag-and-drop when possible. Most file moves can be done through Finder's API (Tier 1), and most list reordering has keyboard shortcuts. Only use coordinate-based dragging as a last resort.

## Localized Error Messages

macOS returns error messages in the system language. If your Mac is set to a non-English language, errors will look different but mean the same thing. Here are common errors in several languages:

| Error (English) | Dutch | French | German | Spanish |
|---|---|---|---|---|
| Not allowed assistive access | Geen toegang voor hulpapparaten | Accès aux fonctions d'assistance non autorisé | Keine Berechtigung für Bedienungshilfen | No se permite el acceso de asistencia |
| No permission to send keystrokes | Geen toestemming om toetsaanslagen te versturen | Pas autorisé à envoyer des frappes | Keine Berechtigung zum Senden von Tastenanschlägen | Sin permiso para enviar pulsaciones |
| Can't get window 1 | Kan venster 1 niet ophalen | Impossible d'obtenir la fenêtre 1 | Fenster 1 kann nicht gelesen werden | No se puede obtener la ventana 1 |
| Application isn't running | Programma is niet actief | L'application n'est pas en cours d'exécution | Programm wird nicht ausgeführt | La aplicación no se está ejecutando |

**How to handle localized errors:**
```applescript
-- Use error number instead of message text for reliable error handling
try
    tell application "System Events" to tell process "Safari"
        click button "Save" of window 1
    end try
on error errMsg number errNum
    if errNum is -1719 then
        -- "Can't get window 1" in any language
        log "No window found"
    else if errNum is -25211 then
        -- Accessibility permission error in any language
        log "Needs accessibility permissions"
    end if
end try
```

**Common error numbers:**
- `-1719` — Element doesn't exist (can't get window/button/etc.)
- `-1728` — Can't get reference
- `-25211` — Not authorized for assistive access
- `-10810` — App not launched / can't connect
- `-1` — General/unknown error (check message text)

## Limitations — When NOT to Use osascript

Be honest about what doesn't work. Don't waste time trying when these apply:

1. **Sandboxed apps that block AppleScript entirely** — Some App Store apps (especially third-party banking, security apps) disable AppleScript completely. No workaround exists.
2. **Complex canvas/drawing apps** — Figma, Photoshop layers, Illustrator paths. The UI elements exist but are impractical to target (hundreds of unnamed groups). Use their own APIs or plugins instead.
3. **Web app content inside browsers** — You can control browser tabs and chrome, but NOT interact with web page DOM elements via System Events. Use JavaScript injection instead: `tell application "Safari" to do JavaScript "document.getElementById('btn').click()" in current tab of window 1`
4. **Games and GPU-rendered UIs** — Metal/OpenGL rendered content has no accessibility tree. Computer use (screenshots) is the only option here.
5. **Touch Bar** — If the Mac has a Touch Bar, those elements aren't reliably scriptable.
6. **Universal Control / Sidecar displays** — Scripts run on the local Mac only. Can't interact with iPad Sidecar content.
7. **FileVault login screen / Lock screen** — No scripting access before the user logs in.
8. **Notarized app restrictions (macOS 15+)** — Some Apple apps are increasingly restricting AppleScript access. Calendar and Reminders may require explicit user permission prompts.

**When computer use (screenshots) IS better:**
- Visually identifying content in images, charts, or non-text UI
- Apps with zero accessibility support
- Verifying that a visual change actually happened (color changed, image loaded)
- Complex drag-and-drop between apps where coordinates matter

## Combining osascript with Shell Commands

Many tasks are best solved by mixing AppleScript with shell commands:

```applescript
-- Get the frontmost app, then use shell to find its preferences file
set appName to (tell application "System Events" to get name of first application process whose frontmost is true)
set prefsPath to do shell script "find ~/Library/Preferences -name '*" & appName & "*' -maxdepth 1 2>/dev/null | head -1"

-- Read a plist value
do shell script "defaults read com.apple.Safari ShowFavoritesBar"

-- Write a plist value (change app behavior)
do shell script "defaults write com.apple.dock autohide -bool true"
do shell script "killall Dock"  -- restart to apply

-- Get screen resolution
do shell script "system_profiler SPDisplaysDataType | grep Resolution"

-- Get connected displays
do shell script "system_profiler SPDisplaysDataType | grep -A2 'Display Type'"

-- CPU/Memory usage of an app
do shell script "ps aux | grep -i safari | head -1 | awk '{print $3, $4}'"

-- Check if an app is installed
do shell script "mdfind 'kMDItemKind == Application' -name 'Slack' | head -1"

-- Get app version
do shell script "defaults read /Applications/Safari.app/Contents/Info CFBundleShortVersionString"
```

## Accessibility Inspector — Your Best Friend

When you can't figure out the UI hierarchy, tell the user to use Accessibility Inspector:

1. Open: `/Applications/Xcode.app/Contents/Developer/Applications/Accessibility Inspector.app` (or `open -a "Accessibility Inspector"`)
2. Click the crosshair button, then hover over any element
3. It shows the exact element type, name, role, and hierarchy path

This is how you debug "can't get button X" errors — the Inspector shows you what the element is actually called.

Alternative without Xcode: `get entire contents of window 1` in System Events, but this is slower and noisier.

## Security Best Practices

When automating on behalf of the user:

1. **Never store passwords in scripts** — use `do shell script "security find-generic-password -w -s 'service' -a 'account'"` to read from Keychain
2. **Don't automate admin password entry** — if something needs sudo, ask the user to run it manually
3. **Be transparent about what you're doing** — before clicking "Delete" or "Send", tell the user what you're about to do
4. **Check before destructive actions** — `get name of every item of selection` before `delete selection`
5. **Don't dismiss security dialogs automatically** — if macOS shows a permission/security prompt, let the user handle it

## App-Specific Recipes

See `references/apps.md` for tested, ready-to-use patterns for 18 popular macOS apps including Finder, Safari, Chrome, Arc, Mail, Messages, Notes, Calendar, System Settings, Terminal, VS Code, Slack, Spotify, Preview, TextEdit, Zoom, Discord, and Microsoft Teams.

Read that file when working with any of these apps — each has its own quirks and optimal patterns.
