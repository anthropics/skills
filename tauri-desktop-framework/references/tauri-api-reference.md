# Tauri API Reference

Complete reference for @tauri-apps/api v2.x TypeScript/JavaScript APIs.

## Installation

```bash
npm install @tauri-apps/api
# or
yarn add @tauri-apps/api
# or
pnpm add @tauri-apps/api
```

---

## Core Modules

### tauri

Main module for invoking backend commands.

```typescript
import { invoke } from '@tauri-apps/api/tauri';

// Invoke command without parameters
const result = await invoke<string>('my_command');

// Invoke command with parameters
const result = await invoke<ReturnType>('command_name', {
    param1: 'value1',
    param2: 123
});

// Error handling
try {
    const data = await invoke<Data>('fetch_data');
} catch (error) {
    console.error('Command failed:', error);
}
```

**Type Safety:**
```typescript
interface User {
    id: number;
    name: string;
}

const user = await invoke<User>('get_user', { userId: 1 });
// user is typed as User
```

---

### window

Window management and control.

```typescript
import { Window, LogicalSize, LogicalPosition } from '@tauri-apps/api/window';

// Get current window
const appWindow = Window.getCurrent();

// Get specific window by label
const settingsWindow = Window.getByLabel('settings');

// Get all windows
const allWindows = Window.getAll();
```

**Window State:**
```typescript
// Minimize, maximize, restore
await appWindow.minimize();
await appWindow.maximize();
await appWindow.unmaximize();
await appWindow.toggleMaximize();

// Show, hide, focus
await appWindow.show();
await appWindow.hide();
await appWindow.setFocus();

// Close
await appWindow.close();

// Fullscreen
await appWindow.setFullscreen(true);
const isFullscreen = await appWindow.isFullscreen();
```

**Window Properties:**
```typescript
// Title
await appWindow.setTitle('New Title');
const title = await appWindow.title();

// Size
await appWindow.setSize(new LogicalSize(1024, 768));
const size = await appWindow.innerSize();
const outerSize = await appWindow.outerSize();

// Position
await appWindow.setPosition(new LogicalPosition(100, 100));
const position = await appWindow.innerPosition();
const outerPosition = await appWindow.outerPosition();

// Min/Max size
await appWindow.setMinSize(new LogicalSize(800, 600));
await appWindow.setMaxSize(new LogicalSize(1920, 1080));

// Other properties
await appWindow.setResizable(false);
await appWindow.setDecorations(true);
await appWindow.setAlwaysOnTop(true);
await appWindow.setSkipTaskbar(false);
await appWindow.setCursorGrab(true);
await appWindow.setCursorVisible(false);
```

**Window Queries:**
```typescript
const isMaximized = await appWindow.isMaximized();
const isMinimized = await appWindow.isMinimized();
const isVisible = await appWindow.isVisible();
const isDecorated = await appWindow.isDecorated();
const isResizable = await appWindow.isResizable();
const scaleFactor = await appWindow.scaleFactor();
```

**Window Events:**
```typescript
import { listen } from '@tauri-apps/api/event';

// Listen for window events
const unlisten = await appWindow.listen('tauri://resize', (event) => {
    console.log('Window resized:', event.payload);
});

// Built-in window events:
// - tauri://resize
// - tauri://move
// - tauri://close-requested
// - tauri://focus
// - tauri://blur
// - tauri://scale-change
// - tauri://menu
// - tauri://file-drop
// - tauri://file-drop-hover
// - tauri://file-drop-cancelled

// Cleanup
unlisten();
```

---

### event

Event system for cross-process communication.

```typescript
import { listen, once, emit } from '@tauri-apps/api/event';
```

**Listening to Events:**
```typescript
// Listen to event
const unlisten = await listen<PayloadType>('event-name', (event) => {
    console.log('Event received:', event.payload);
    console.log('Event ID:', event.id);
    console.log('Window label:', event.windowLabel);
});

// Listen once
const unlistenOnce = await once<PayloadType>('event-name', (event) => {
    console.log('One-time event:', event.payload);
});

// Cleanup
unlisten();
```

**Emitting Events:**
```typescript
import { emit } from '@tauri-apps/api/event';

// Emit to all windows
await emit('notification', { message: 'Hello!' });

// Emit to specific window
import { Window } from '@tauri-apps/api/window';
const targetWindow = Window.getByLabel('main');
await targetWindow.emit('data-update', { data: newData });
```

**Event Payload Types:**
```typescript
interface NotificationPayload {
    title: string;
    message: string;
    severity: 'info' | 'warning' | 'error';
}

const unlisten = await listen<NotificationPayload>('notification', (event) => {
    const { title, message, severity } = event.payload;
    showNotification(title, message, severity);
});
```

---

### fs (File System)

Secure file system operations.

```typescript
import {
    readTextFile,
    readBinaryFile,
    writeTextFile,
    writeBinaryFile,
    exists,
    createDir,
    removeFile,
    removeDir,
    renameFile,
    copyFile,
    readDir,
    BaseDirectory
} from '@tauri-apps/api/fs';
```

**Reading Files:**
```typescript
// Read text file
const contents = await readTextFile('config.json', {
    dir: BaseDirectory.AppConfig
});

// Read binary file
const bytes = await readBinaryFile('image.png', {
    dir: BaseDirectory.AppData
});

// Read from custom path
const data = await readTextFile('/absolute/path/to/file.txt');
```

**Writing Files:**
```typescript
// Write text file
await writeTextFile('data.json', JSON.stringify(data), {
    dir: BaseDirectory.AppData
});

// Write binary file
await writeBinaryFile('output.bin', new Uint8Array([1, 2, 3, 4]), {
    dir: BaseDirectory.Download
});

// Append to file
await writeTextFile('log.txt', 'New log entry\n', {
    dir: BaseDirectory.AppLog,
    append: true
});
```

**Directory Operations:**
```typescript
// Create directory
await createDir('my-folder', {
    dir: BaseDirectory.AppData,
    recursive: true
});

// Read directory
const entries = await readDir('my-folder', {
    dir: BaseDirectory.AppData,
    recursive: false
});

for (const entry of entries) {
    console.log(entry.name, entry.path);
    if (entry.children) {
        // Directory with children
    }
}

// Check existence
const fileExists = await exists('config.json', {
    dir: BaseDirectory.AppConfig
});
```

**File Operations:**
```typescript
// Copy file
await copyFile('source.txt', 'destination.txt', {
    dir: BaseDirectory.AppData
});

// Rename file
await renameFile('old.txt', 'new.txt', {
    dir: BaseDirectory.AppData
});

// Remove file
await removeFile('temp.txt', {
    dir: BaseDirectory.Temp
});

// Remove directory
await removeDir('temp-folder', {
    dir: BaseDirectory.Temp,
    recursive: true
});
```

**Base Directories:**
```typescript
// Available directories:
BaseDirectory.Audio          // Platform-specific audio directory
BaseDirectory.Cache          // Platform-specific cache directory
BaseDirectory.Config         // Platform-specific config directory
BaseDirectory.Data           // Platform-specific data directory
BaseDirectory.LocalData      // Platform-specific local data directory
BaseDirectory.Desktop        // User's desktop directory
BaseDirectory.Document       // User's document directory
BaseDirectory.Download       // User's download directory
BaseDirectory.Picture        // User's picture directory
BaseDirectory.Public         // User's public directory
BaseDirectory.Video          // User's video directory
BaseDirectory.Resource       // Application resource directory
BaseDirectory.Temp           // Temporary directory
BaseDirectory.AppConfig      // App-specific config directory
BaseDirectory.AppData        // App-specific data directory
BaseDirectory.AppLocalData   // App-specific local data directory
BaseDirectory.AppCache       // App-specific cache directory
BaseDirectory.AppLog         // App-specific log directory
```

---

### dialog

Native file and message dialogs.

```typescript
import { open, save, message, ask, confirm } from '@tauri-apps/api/dialog';
```

**File Dialogs:**
```typescript
// Open file dialog
const selected = await open({
    multiple: false,
    filters: [{
        name: 'Image',
        extensions: ['png', 'jpeg', 'jpg', 'gif']
    }]
});

// Open multiple files
const files = await open({
    multiple: true,
    filters: [{
        name: 'Text',
        extensions: ['txt', 'md']
    }]
});

// Open directory
const directory = await open({
    directory: true,
    multiple: false,
    defaultPath: '/home/user/documents'
});

// Save file dialog
const savePath = await save({
    filters: [{
        name: 'JSON',
        extensions: ['json']
    }],
    defaultPath: 'data.json'
});
```

**Message Dialogs:**
```typescript
// Show message
await message('Operation completed successfully!', {
    title: 'Success',
    type: 'info'
});

// Show error
await message('An error occurred', {
    title: 'Error',
    type: 'error'
});

// Ask question (OK/Cancel)
const answer = await ask('Do you want to continue?', {
    title: 'Confirmation',
    type: 'warning'
});

// Confirm (Yes/No)
const confirmed = await confirm('Are you sure you want to delete this?', {
    title: 'Delete Confirmation',
    type: 'warning'
});
```

**Dialog Options:**
```typescript
interface DialogFilter {
    name: string;
    extensions: string[];
}

interface OpenDialogOptions {
    defaultPath?: string;
    directory?: boolean;
    multiple?: boolean;
    filters?: DialogFilter[];
    title?: string;
}

interface SaveDialogOptions {
    defaultPath?: string;
    filters?: DialogFilter[];
    title?: string;
}
```

---

### path

Path manipulation utilities.

```typescript
import {
    appConfigDir,
    appDataDir,
    appLocalDataDir,
    appCacheDir,
    appLogDir,
    audioDir,
    cacheDir,
    configDir,
    dataDir,
    desktopDir,
    documentDir,
    downloadDir,
    pictureDir,
    publicDir,
    runtimeDir,
    tempDir,
    videoDir,
    resourceDir,
    resolve,
    join,
    dirname,
    basename,
    extname,
    sep
} from '@tauri-apps/api/path';
```

**Getting Platform Directories:**
```typescript
// App-specific directories
const appConfig = await appConfigDir();  // e.g., /home/user/.config/my-app
const appData = await appDataDir();      // e.g., /home/user/.local/share/my-app
const appCache = await appCacheDir();    // e.g., /home/user/.cache/my-app
const appLog = await appLogDir();        // e.g., /home/user/.local/share/my-app/logs

// User directories
const desktop = await desktopDir();      // e.g., /home/user/Desktop
const documents = await documentDir();   // e.g., /home/user/Documents
const downloads = await downloadDir();   // e.g., /home/user/Downloads
const pictures = await pictureDir();     // e.g., /home/user/Pictures

// System directories
const temp = await tempDir();            // e.g., /tmp
const cache = await cacheDir();          // e.g., /home/user/.cache
```

**Path Manipulation:**
```typescript
// Join paths
const fullPath = await join(await appDataDir(), 'database', 'data.db');
// Result: /home/user/.local/share/my-app/database/data.db

// Resolve path
const resolved = await resolve('..', 'other-file.txt');

// Get directory name
const dir = await dirname('/path/to/file.txt');  // /path/to

// Get base name
const base = await basename('/path/to/file.txt');  // file.txt

// Get extension
const ext = await extname('/path/to/file.txt');  // .txt

// Path separator
const pathSep = await sep();  // '/' on Unix, '\' on Windows
```

---

### http

HTTP client for making requests.

```typescript
import { fetch, Body, Client, ResponseType } from '@tauri-apps/api/http';
```

**Simple Requests:**
```typescript
// GET request
const response = await fetch<Data>('https://api.example.com/data', {
    method: 'GET',
    timeout: 30
});

console.log(response.status);  // 200
console.log(response.data);    // Typed as Data
console.log(response.headers); // Response headers

// POST request with JSON
const response = await fetch('https://api.example.com/users', {
    method: 'POST',
    headers: {
        'Content-Type': 'application/json'
    },
    body: Body.json({
        name: 'John Doe',
        email: 'john@example.com'
    })
});

// POST request with form data
const formData = {
    username: 'john',
    password: 'secret'
};

const response = await fetch('https://api.example.com/login', {
    method: 'POST',
    body: Body.form(formData)
});
```

**Advanced Client:**
```typescript
const client = await new Client({
    maxRedirections: 5,
    connectTimeout: 30
});

try {
    const response = await client.get<Data>('https://api.example.com/data', {
        headers: {
            'Authorization': 'Bearer token',
            'User-Agent': 'MyApp/1.0'
        },
        responseType: ResponseType.JSON
    });

    console.log(response.data);
} finally {
    await client.drop();  // Clean up client
}
```

---

### shell

Execute shell commands and scripts.

```typescript
import { Command } from '@tauri-apps/api/shell';
```

**Execute Commands:**
```typescript
// Simple command
const output = await new Command('ls', ['-la']).execute();

console.log(output.code);    // Exit code
console.log(output.stdout);  // Standard output
console.log(output.stderr);  // Standard error

// Command with environment variables
const output = await new Command('python', ['script.py'], {
    env: {
        'PYTHONPATH': '/custom/path',
        'DEBUG': 'true'
    }
}).execute();

// Stream output
const command = new Command('long-running-process');

command.on('close', (data) => {
    console.log('Process exited with code:', data.code);
});

command.on('error', (error) => {
    console.error('Process error:', error);
});

command.stdout.on('data', (line) => {
    console.log('stdout:', line);
});

command.stderr.on('data', (line) => {
    console.error('stderr:', line);
});

await command.spawn();
```

---

### clipboard

Clipboard operations.

```typescript
import { writeText, readText } from '@tauri-apps/api/clipboard';

// Write to clipboard
await writeText('Hello, clipboard!');

// Read from clipboard
const text = await readText();
console.log(text);  // "Hello, clipboard!"
```

---

### notification

System notifications.

```typescript
import { sendNotification, requestPermission, isPermissionGranted } from '@tauri-apps/api/notification';

// Check and request permission
let permissionGranted = await isPermissionGranted();
if (!permissionGranted) {
    const permission = await requestPermission();
    permissionGranted = permission === 'granted';
}

// Send notification
if (permissionGranted) {
    sendNotification({
        title: 'Task Complete',
        body: 'Your task has finished processing',
        icon: 'icons/notification.png'
    });
}
```

---

### globalShortcut

Register global keyboard shortcuts.

```typescript
import { register, unregister, isRegistered, unregisterAll } from '@tauri-apps/api/globalShortcut';

// Register shortcut
await register('CommandOrControl+Shift+C', () => {
    console.log('Shortcut triggered!');
});

// Check if registered
const registered = await isRegistered('CommandOrControl+Shift+C');

// Unregister specific shortcut
await unregister('CommandOrControl+Shift+C');

// Unregister all shortcuts
await unregisterAll();
```

**Shortcut Modifiers:**
- `Command` / `Cmd` (macOS only)
- `Control` / `Ctrl`
- `CommandOrControl` / `CmdOrCtrl` (Cmd on macOS, Ctrl elsewhere)
- `Alt` / `Option`
- `Shift`
- `Super` (Windows key on Windows/Linux, Cmd on macOS)

---

### updater

Application auto-updater.

```typescript
import { checkUpdate, installUpdate } from '@tauri-apps/api/updater';
import { relaunch } from '@tauri-apps/api/process';

// Check for updates
const { shouldUpdate, manifest } = await checkUpdate();

if (shouldUpdate) {
    console.log(`Update available: ${manifest?.version}`);
    console.log(`Release notes: ${manifest?.body}`);
    console.log(`Release date: ${manifest?.date}`);

    // Install update
    await installUpdate();

    // Relaunch application
    await relaunch();
}
```

---

## Type Definitions

**Common Types:**
```typescript
interface InvokeOptions {
    headers?: Record<string, string>;
}

interface EventCallback<T> {
    (event: Event<T>): void;
}

interface Event<T> {
    id: number;
    windowLabel: string;
    payload: T;
}

interface UnlistenFn {
    (): void;
}

type Theme = 'light' | 'dark';

class LogicalSize {
    width: number;
    height: number;
    constructor(width: number, height: number);
}

class PhysicalSize {
    width: number;
    height: number;
    constructor(width: number, height: number);
}

class LogicalPosition {
    x: number;
    y: number;
    constructor(x: number, y: number);
}

class PhysicalPosition {
    x: number;
    y: number;
    constructor(x: number, y: number);
}
```

---

## References

- Official API Docs: https://v2.tauri.app/reference/javascript/api/
- NPM Package: https://www.npmjs.com/package/@tauri-apps/api
- GitHub: https://github.com/tauri-apps/tauri
