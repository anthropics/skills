# App-Specific Recipes

Tested AppleScript patterns for popular macOS apps. Each section shows the correct process name, common UI hierarchy, and ready-to-use scripts.

**Permission key:** Recipes marked with **[Tier 1]** work out of the box. Recipes marked with **[Tier 2]** require Accessibility permissions in System Settings → Privacy & Security → Accessibility. Always prefer Tier 1 patterns.

## Table of Contents
1. [Finder](#finder)
2. [Safari](#safari)
3. [Google Chrome](#google-chrome)
4. [Mail](#mail)
5. [Messages](#messages)
6. [Notes](#notes)
7. [Calendar](#calendar)
8. [System Settings](#system-settings)
9. [Terminal](#terminal)
10. [VS Code](#vs-code)
11. [Slack](#slack)
12. [Spotify](#spotify)
13. [Preview](#preview)
14. [TextEdit](#textedit)

---

## Finder

Process name: `Finder`

Finder has its own rich AppleScript dictionary — you can often talk to it directly without System Events.
```applescript
-- Open a folder
tell application "Finder"
    open folder "Documents" of home
end tell

-- Get selected files
tell application "Finder"
    get selection
end tell

-- Get names of selected files
tell application "Finder"
    get name of every item of selection
end tell

-- Create a new folder
tell application "Finder"
    make new folder at desktop with properties {name:"New Folder"}
end tell

-- Move a file
tell application "Finder"
    move file "test.txt" of desktop to folder "Documents" of home
end tell

-- Duplicate a file
tell application "Finder"
    duplicate file "test.txt" of desktop
end tell
-- Trash a file
tell application "Finder"
    move file "test.txt" of desktop to trash
end tell

-- Get file info
tell application "Finder"
    get {name, size, modification date} of file "test.txt" of desktop
end tell

-- Open a file with a specific app
tell application "Finder"
    open file "document.pdf" of desktop using application "Preview"
end tell

-- List contents of a folder
tell application "Finder"
    get name of every item of folder "Documents" of home
end tell

-- Open a new Finder window at a path
tell application "Finder"
    make new Finder window
    set target of Finder window 1 to POSIX file "/Users/username/Desktop"
end tell

-- Toggle hidden files
do shell script "defaults read com.apple.finder AppleShowAllFiles"
-- Toggle: defaults write com.apple.finder AppleShowAllFiles -bool true && killall Finder
```
---

## Safari

Process name: `Safari`

Safari has a rich AppleScript dictionary for tab/window management.

```applescript
-- Open a URL
tell application "Safari"
    activate
    open location "https://example.com"
end tell

-- Open URL in new tab
tell application "Safari"
    tell window 1
        set current tab to (make new tab with properties {URL:"https://example.com"})
    end tell
end tell

-- Get current URL
tell application "Safari"
    get URL of current tab of window 1
end tell

-- Get page title
tell application "Safari"
    get name of current tab of window 1
end tell
-- Get all tab URLs
tell application "Safari"
    get URL of every tab of window 1
end tell

-- Get page text content
tell application "Safari"
    get text of current tab of window 1
end tell

-- Run JavaScript
tell application "Safari"
    do JavaScript "document.title" in current tab of window 1
end tell

-- Click an element via JavaScript
tell application "Safari"
    do JavaScript "document.querySelector('button.submit').click()" in current tab of window 1
end tell

-- Fill a form field via JavaScript
tell application "Safari"
    do JavaScript "document.getElementById('email').value = 'user@example.com'" in current tab of window 1
end tell

-- Close current tab
tell application "Safari"
    close current tab of window 1
end tell
-- Switch to a specific tab
tell application "Safari"
    set current tab of window 1 to tab 3 of window 1
end tell

-- Go back/forward
tell application "System Events" to tell process "Safari"
    keystroke "[" using command down  -- back
    keystroke "]" using command down  -- forward
end tell
```

---

## Google Chrome

Process name: `Google Chrome`

Chrome also has AppleScript support for tabs and JavaScript.

```applescript
-- Open a URL
tell application "Google Chrome"
    activate
    open location "https://example.com"
end tell

-- Open in new tab
tell application "Google Chrome"
    tell window 1
        make new tab with properties {URL:"https://example.com"}
    end tell
end tell
-- Get current URL
tell application "Google Chrome"
    get URL of active tab of window 1
end tell

-- Get page title
tell application "Google Chrome"
    get title of active tab of window 1
end tell

-- Run JavaScript
tell application "Google Chrome"
    execute active tab of window 1 javascript "document.title"
end tell

-- Get all tab titles
tell application "Google Chrome"
    get title of every tab of window 1
end tell

-- Close current tab
tell application "Google Chrome"
    close active tab of window 1
end tell
```

---

## Mail

Process name: `Mail`

```applescript-- Get unread count
tell application "Mail"
    get unread count of inbox
end tell

-- Read recent messages
tell application "Mail"
    set msgs to messages 1 thru 5 of inbox
    repeat with m in msgs
        get {sender, subject, date received} of m
    end repeat
end tell

-- Read a specific message's content
tell application "Mail"
    get content of message 1 of inbox
end tell

-- Compose a new email
tell application "Mail"
    set newMsg to make new outgoing message with properties {subject:"Hello", content:"Message body here", visible:true}
    tell newMsg
        make new to recipient at end of to recipients with properties {address:"user@example.com"}
    end tell
    activate
end tell

-- Send a composed email (add `send newMsg` after making it)
tell application "Mail"
    set newMsg to make new outgoing message with properties {subject:"Hello", content:"Body"}
    tell newMsg        make new to recipient at end of to recipients with properties {address:"user@example.com"}
    end tell
    send newMsg
end tell

-- Check for new mail
tell application "Mail"
    check for new mail
end tell

-- Search mail
tell application "Mail"
    get messages of inbox whose subject contains "invoice"
end tell
```

---
## Messages

Process name: `Messages`

```applescript
-- Send an iMessage
tell application "Messages"
    set targetBuddy to "+1234567890"
    set targetService to 1st account whose service type = iMessage
    set theBuddy to participant targetBuddy of targetService
    send "Hello!" to theBuddy
end tell

-- Read recent messages (via shell — Messages.app scripting is limited)
do shell script "sqlite3 ~/Library/Messages/chat.db \"SELECT text FROM message ORDER BY date DESC LIMIT 5;\""
```

Note: Messages automation is limited. For reading messages, the iMessages MCP (`mcp__Read_and_Send_iMessages__read_imessages`) may be more reliable if available.

---

## Notes

Process name: `Notes`

```applescript
-- Create a new note
tell application "Notes"
    tell account "iCloud"
        make new note at folder "Notes" with properties {name:"My Note", body:"Note content here"}
    end tell
end tell
-- List recent notes
tell application "Notes"
    get name of every note of account "iCloud"
end tell

-- Read a note's content
tell application "Notes"
    get body of note "My Note" of account "iCloud"
end tell

-- Search notes
tell application "Notes"
    get name of every note of account "iCloud" whose name contains "meeting"
end tell
```

Note: The Apple Notes MCP (`mcp__Read_and_Write_Apple_Notes__*`) may also be available for richer note interactions.

---

## Calendar

Process name: `Calendar`

```applescript
-- Get today's events
tell application "Calendar"
    set today to current date
    set todayStart to today - (time of today)
    set todayEnd to todayStart + (1 * days)
    get {summary, start date, end date} of every event of calendar "Home" whose start date ≥ todayStart and start date < todayEnd
end tell
-- Create an event
tell application "Calendar"
    tell calendar "Home"
        set startDate to current date
        set hours of startDate to 14
        set minutes of startDate to 0
        set endDate to startDate + (1 * hours)
        make new event with properties {summary:"Meeting", start date:startDate, end date:endDate}
    end tell
end tell

-- List calendars
tell application "Calendar"
    get name of every calendar
end tell
```

---

## System Settings

Process name: `System Settings` (macOS Ventura+) or `System Preferences` (older)

System Settings is trickier because Apple redesigned it. UI navigation via System Events works:

```applescript
-- Open System Settings
tell application "System Settings" to activate

-- Navigate to a specific pane (use UI clicking)
tell application "System Events" to tell process "System Settings"
    -- Wait for window
    delay 0.5    -- Click a sidebar item
    -- Discovery is often needed here:
    get every UI element of window 1
end tell

-- Open a specific pane by URL scheme
open location "x-apple.systempreferences:com.apple.preference.network"

-- Toggle Wi-Fi via shell (more reliable)
do shell script "networksetup -setairportpower en0 off"
do shell script "networksetup -setairportpower en0 on"

-- Check Wi-Fi status
do shell script "networksetup -getairportpower en0"
```

---

## Terminal

Process name: `Terminal`

```applescript
-- Run a command in Terminal
tell application "Terminal"
    activate
    do script "ls -la"
end tell

-- Run a command in a new tab
tell application "Terminal"
    activate
    tell application "System Events" to keystroke "t" using command down    delay 0.3
    do script "cd ~/Projects" in front window
end tell

-- Get Terminal output (read the content)
tell application "Terminal"
    get contents of selected tab of window 1
end tell
```

---

## VS Code

Process name: `Code` (note: not "VS Code" or "Visual Studio Code")

VS Code is best controlled via keyboard shortcuts through System Events:
```applescript
-- Open command palette
tell application "Code" to activate
tell application "System Events" to tell process "Code"
    keystroke "p" using {command down, shift down}
    delay 0.3
    keystroke "your command here"
    keystroke return
end tell

-- Open a file
tell application "Code" to activate
tell application "System Events" to tell process "Code"
    keystroke "p" using command down  -- Quick Open
    delay 0.3
    keystroke "filename.js"
    delay 0.3
    keystroke return
end tell

-- Toggle terminal
tell application "System Events" to tell process "Code"
    keystroke "`" using control down
end tell

-- Save file
tell application "System Events" to tell process "Code"
    keystroke "s" using command down
end tell

-- Open a folder via shell
do shell script "open -a 'Visual Studio Code' /path/to/folder"
```
---

## Slack

Process name: `Slack`

```applescript
-- Jump to a channel
tell application "Slack" to activate
tell application "System Events" to tell process "Slack"
    keystroke "k" using command down  -- Quick switcher
    delay 0.3
    keystroke "general"
    delay 0.5
    keystroke return
end tell

-- Send a message (type into the message field)
tell application "System Events" to tell process "Slack"
    -- Message field is usually focused when in a channel
    keystroke "Hello team!"
    keystroke return
end tell

-- Search
tell application "System Events" to tell process "Slack"
    keystroke "g" using command down
    delay 0.3
    keystroke "search query"
end tell
```

Note: The Slack MCP (`mcp__slack__*`) is much more reliable for Slack operations if available.
---

## Spotify

Process name: `Spotify`

Spotify has a built-in AppleScript dictionary:

```applescript
-- Play/pause
tell application "Spotify" to playpause

-- Next track
tell application "Spotify" to next track

-- Previous track
tell application "Spotify" to previous track

-- Get current track info
tell application "Spotify"
    get {name, artist, album} of current track
end tell

-- Set volume (0-100)
tell application "Spotify"
    set sound volume to 50
end tell

-- Play a specific URI
tell application "Spotify"
    play track "spotify:track:TRACK_ID"
end tell
-- Get player state
tell application "Spotify"
    get player state  -- playing, paused, stopped
end tell
```

---

## Preview

Process name: `Preview`

```applescript
-- Open a file
tell application "Preview"
    open POSIX file "/path/to/document.pdf"
    activate
end tell

-- Zoom in/out
tell application "System Events" to tell process "Preview"
    keystroke "+" using command down  -- zoom in
    keystroke "-" using command down  -- zoom out
    keystroke "0" using command down  -- actual size
end tell
```

---

## TextEdit

Process name: `TextEdit`

```applescript
-- Create a new document with text
tell application "TextEdit"
    activate
    make new document with properties {text:"Hello, world!"}
end tell
-- Read document text
tell application "TextEdit"
    get text of document 1
end tell

-- Set document text
tell application "TextEdit"
    set text of document 1 to "New content"
end tell
```