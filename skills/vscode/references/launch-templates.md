# VS Code Launch Configurations Templates

Ready-to-use `launch.json` templates for the most common debug scenarios. Use the skill's `launch init --template <name> --ProjectPath <path>` command to copy a template into `<project>/.vscode/launch.json`.

For variables and the full schema, see the live docs at <https://code.visualstudio.com/docs/editor/debugging>.

## Available Templates

| Template ID | Language | Purpose |
|---|---|---|
| `node-current-file` | Node.js | Debug the currently active JavaScript file. |
| `node-mocha` | Node.js | Run and debug Mocha tests. |
| `python-current-file` | Python | Debug the currently active Python file. |
| `python-pytest` | Python | Debug a single pytest run. |
| `python-flask` | Python | Debug a Flask app. |
| `go-current-file` | Go | Debug the currently active Go file. |
| `rust-current-file` | Rust | Debug the currently active Rust binary. |
| `chrome-launch` | Browser | Launch Chrome against an HTML file. |
| `chrome-attach` | Browser | Attach to an already-running Chrome instance. |

## Per-Template Details

### `node-current-file`

Runs the active JavaScript / TypeScript file with the workspace folder as `cwd`.

Variables:

* `runtimeExecutable` — node binary (default: `node`).
* `runtimeArgs` — extra node args (default: empty).

### `node-mocha`

Runs Mocha with the workspace's test files.

Variables:

* `mocha.tests` — glob for tests (default: `${workspaceFolder}/test/**/*.js`).

### `python-current-file`

Uses the project's selected Python interpreter.

Variables:

* `python.args` — extra args passed to the script.

### `python-pytest`

Debugs pytest with the active test file.

Variables:

* `pytest.args` — extra pytest args (default: `-v`).

### `python-flask`

Launches a Flask app with debug mode.

Variables:

* `flask.app` — entry point (default: `app.py`).

### `go-current-file`

Uses `dlv` (delve) to debug the current Go file.

Variables:

* `go.file` — file to debug (default: `${file}`).

### `rust-current-file`

Debugs the currently active Rust file using `lldb`.

### `chrome-launch`

Launches Chrome against the workspace's `index.html`.

Variables:

* `url` — URL to open (default: `http://localhost:3000`).

### `chrome-attach`

Attaches to a Chrome instance started with `--remote-debugging-port=9222`.

Variables:

* `url` — URL to attach to (default: `http://localhost:9222`).

## Usage

```powershell
# Windows / PowerShell
pwsh -File scripts/vscode-cli.ps1 launch init --Template python-pytest --ProjectPath D:\projects\demo --Apply

# Cross-platform
python scripts/vscode_skill.py launch init --Template python-pytest --ProjectPath /path/to/demo --Apply
```

The command:

1. Resolves the template under `references/templates/launch/<id>.json`.
2. Writes `<project>/.vscode/launch.json` (creating the directory if missing).
3. Refuses to overwrite an existing file unless `--Force` is passed.

## Adding Your Own

Drop a JSON file at `references/templates/launch/<your-id>.json` and the `launch init --list` command will pick it up automatically. Keep the schema compatible with VS Code's `launch.json` schema (version 0.2.0).