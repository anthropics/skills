# Common contribution points (command-type extensions)

Quick reference for wiring up `package.json` `contributes` + `src/extension.ts`
for the most common things a user asks a VS Code extension to do. Only add
what's needed for the request — don't include unused contribution points.

## Command (already scaffolded)

`package.json`:
```json
"contributes": {
  "commands": [{ "command": "<name>.doThing", "title": "Do Thing" }]
}
```
`extension.ts`:
```ts
context.subscriptions.push(
  vscode.commands.registerCommand('<name>.doThing', () => { /* ... */ })
);
```

## Keybinding

```json
"contributes": {
  "keybindings": [
    { "command": "<name>.doThing", "key": "ctrl+alt+d", "mac": "cmd+alt+d", "when": "editorTextFocus" }
  ]
}
```

## Menu item (editor context menu, command palette, etc.)

```json
"contributes": {
  "menus": {
    "editor/context": [{ "command": "<name>.doThing", "when": "editorTextFocus", "group": "navigation" }]
  }
}
```

## Status bar item

```ts
const item = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
item.text = '$(rocket) My Status';
item.command = '<name>.doThing';
item.show();
context.subscriptions.push(item);
```

## Configuration setting

```json
"contributes": {
  "configuration": {
    "title": "<Display Name>",
    "properties": {
      "<name>.someSetting": {
        "type": "boolean",
        "default": true,
        "description": "What this setting controls."
      }
    }
  }
}
```
```ts
const value = vscode.workspace.getConfiguration('<name>').get<boolean>('someSetting');
```

## Webview panel

```ts
const panel = vscode.window.createWebviewPanel(
  '<name>.panel',
  'Panel Title',
  vscode.ViewColumn.One,
  { enableScripts: true }
);
panel.webview.html = `<!DOCTYPE html><html><body><h1>Hello</h1></body></html>`;
```

## Tree view (sidebar panel)

```json
"contributes": {
  "views": {
    "explorer": [{ "id": "<name>.view", "name": "<Display Name>" }]
  }
}
```
```ts
class MyProvider implements vscode.TreeDataProvider<vscode.TreeItem> {
  getTreeItem(el: vscode.TreeItem) { return el; }
  getChildren() { return [new vscode.TreeItem('Example')]; }
}
vscode.window.registerTreeDataProvider('<name>.view', new MyProvider());
```

## React to file/workspace changes

```ts
const watcher = vscode.workspace.createFileSystemWatcher('**/*.ext');
watcher.onDidChange(uri => { /* ... */ });
context.subscriptions.push(watcher);

vscode.workspace.onDidSaveTextDocument(doc => { /* run on save */ });
```

## Format-on-save / document formatter

```ts
vscode.languages.registerDocumentFormattingEditProvider('<languageId>', {
  provideDocumentFormattingEdits(document) {
    // return vscode.TextEdit[]
  }
});
```

## Activation events

Since VS Code 1.74+, `onCommand`, `onLanguage`, and most other activation
events are inferred automatically from `contributes` — leave
`activationEvents: []` unless activation needs to happen on something that
can't be inferred (e.g. `onStartupFinished`, `onFileSystem:<scheme>`).
