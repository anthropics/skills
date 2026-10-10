---
name: eppie-email-cli
description: Use this skill when the task requires running eppie-console to work with email. Covers Gmail, Outlook, Proton Mail, IMAP/SMTP, and decentralized Eppie mail. Trigger when the user asks to read, send, or delete email messages; check an inbox or mail folder; sync a mailbox; add or list email accounts; initialize or reset the local vault; or automate any email workflow through the eppie-console CLI. Do not use for conceptual explanations without running commands.
---

# Eppie CLI agent skill

Use this skill when an autonomous or semi-autonomous agent must operate `eppie-console` directly.

`eppie-console` is a console mail client that can work with:
- Gmail,
- Outlook,
- Proton Mail,
- regular IMAP/SMTP email services,
- decentralized peer-to-peer Eppie mail.

## Purpose

Use `eppie-console` in a predictable, automation-friendly way to:
- inspect accounts,
- inspect folders,
- read messages,
- send messages,
- sync folders,
- initialize, unlock, and reset the local vault when needed by the task.

This skill focuses on deterministic command execution, structured output handling, and explicit standard-input contracts.

For end-to-end validation, coverage, and reproducible test scenarios, use `eppie-cli-agent-test-plan.md`.

## How to use this file

Treat sections marked `Normative` as the required contract for agent execution.
Treat sections marked `Reference` as supporting material, examples, or quick navigation aids.

Normative sections in this file:
- `Normative defaults for agents`
- `Normative rules`
- `Normative command patterns for agents`
- `Normative stdin contracts`
- `Normative execution policy for autonomous agents`
- `Normative error handling`

Reference sections in this file:
- `Reference: preferred installation`
- `Reference: required inputs`
- `Reference: launch modes`
- `Reference: decision guide`
- `Reference: end-to-end agent scenarios`
- `Reference: command-specific notes and examples`
- `Reference: recommended agent workflow`
- `Reference: known limitations`
- `Reference: contributing`

## Normative defaults for agents

When the task requires executing `eppie-console`, use these defaults unless the task explicitly requires otherwise:

1. use `--non-interactive=true`
2. use `--output=json` for agent automation unless text output is explicitly required
3. use `--unlock-password-stdin=true` for stateful commands that need an existing vault
4. use `--assume-yes=true` for destructive automation
5. provide `stdin` exactly in the required order
6. use one consistent working directory per vault

Canonical command patterns and exact `stdin` contracts are defined later in this file. Use those sections as the single source of truth for agent execution.

## Use this skill when

- the task requires executing `eppie-console`
- the agent must inspect accounts, folders, messages, or contacts
- the agent must send a message
- the agent must synchronize a folder
- the agent must initialize or reset the local vault
- the agent must work with machine-readable CLI output

## Do not use this skill when

- the task does not require calling `eppie-console`
- the task is only to explain behavior conceptually without running commands
- the task is primarily about test coverage or validation workflows; use `eppie-cli-agent-test-plan.md`
- an interactive REPL session is not explicitly required but would be the only execution path
- the required executable or working directory is unavailable

## Reference: preferred installation

Prefer the executable published in GitHub Releases.
You can also build from source.

Latest release page:
- https://github.com/Eppie-io/Eppie-CLI/releases/latest

Direct download links:

### Linux
- https://github.com/Eppie-io/Eppie-CLI/releases/latest/download/Eppie.CLI-linux-x64.tar.gz
- https://github.com/Eppie-io/Eppie-CLI/releases/latest/download/Eppie.CLI-linux-arm64.tar.gz

### macOS
- https://github.com/Eppie-io/Eppie-CLI/releases/latest/download/Eppie.CLI-osx-x64.tar.gz
- https://github.com/Eppie-io/Eppie-CLI/releases/latest/download/Eppie.CLI-osx-arm64.tar.gz

### Windows
- https://github.com/Eppie-io/Eppie-CLI/releases/latest/download/Eppie.CLI-win-x64.zip
- https://github.com/Eppie-io/Eppie-CLI/releases/latest/download/Eppie.CLI-win-arm64.zip

After extracting the archive, use the `eppie-console` executable directly.

## Reference: required inputs

### Common inputs
- path to `eppie-console`
- working directory
- whether the task requires stateful access to an existing vault
- whether structured JSON output is required

### Vault access inputs
- vault password
- whether the vault must be initialized first

### Reading inputs
- account identifier for `-a`; for agent workflows, use the account address string returned by `list-accounts` in `data[].address`
- folder name when folder-specific access is needed
- message `id`
- message `pk`
- page size and total limit for paged commands

### Sending inputs
- sender address
- receiver address
- subject
- message body

### Account creation inputs
- account type
- vault password
- structured JSON payload when required
- provider-specific secrets only through standard input when supported

## Reference: launch modes

### Interactive mode
Use only when a REPL session is explicitly needed.

Example:
- `eppie-console`

Typical sequence:
- `open`
- vault password
- `list-accounts`
- `exit`

`open` is useful in interactive mode to open the local vault inside the current process.

### Non-interactive mode
Prefer this mode for agents.

Use:
- `eppie-console --non-interactive=true <command> [command options]`

To avoid passing the same startup flags on every call, you can put them in `appsettings.json` next to `eppie-console`, for example:
- `{ "non-interactive": true, "output": "json", "unlock-password-stdin": true }`

`eppie-console` also reads configuration from environment variables.

When the default .NET host configuration pipeline is used, environment variables override `appsettings.json`. Command-line arguments override both.

For structured machine-readable output, also use:
- `--output=json`

JSON responses use a normalized envelope:
- `type`: `result`, `status`, `warning`, or `error`
- `code`: stable machine-readable outcome code
- `data`: payload for `result` and `status` responses
- `meta`: optional metadata for `result` responses; usually `null`, but paged read commands can return objects such as `{"header":"All messages:","returned":5,"hasMore":true}`
- `message`: human-readable warning/error text

In `--non-interactive=true --output=json` mode, structured responses are emitted on `stdout` without a preceding stack trace on `stderr` for handled command failures such as `unhandledException`.

In non-interactive mode, do not use `open` as part of the agent workflow. It does not establish reusable state for later process launches. For stateful non-interactive commands, use `--unlock-password-stdin=true` instead.

For all agent examples in this file, `<account>` means the account address returned by `list-accounts` in `data[].address`. Prefer that address string for `-a` instead of the numeric `id`, unless a command explicitly documents another identifier format.

Common success-output examples:
- `--non-interactive=true --output=json list-accounts` (with accounts):
  - `{"type":"result","code":"accounts","data":[{"id":1,"address":"<address>","accountType":"Dec"}],"meta":null}`
- `--non-interactive=true --assume-yes=true --output=json reset`:
  - `{"type":"status","code":"reset","data":null}`
- `--non-interactive=true --unlock-password-stdin=true --output=json send ...`:
  - `{"type":"status","code":"messageSent","data":{"subject":"<subject>","to":"<receiver>","from":"<sender>"}}`
- `--non-interactive=true --unlock-password-stdin=true --output=json sync-folder ...`:
  - `{"type":"status","code":"folderSynced","data":{"account":"<account>","folder":"Inbox"}}`
- `--non-interactive=true --unlock-password-stdin=true --output=json show-all-messages ...`:
  - `{"type":"result","code":"messages","data":[{"id":1,"pk":1,"to":["<receiver>"],"from":["<sender>"],"folder":"Inbox","subject":"<subject>"}],"meta":{"header":"All messages:","returned":1,"hasMore":false}}`

Additional command-specific JSON result shapes are documented later in `Reference: command-specific notes and examples`.

Common text success-output examples:
- `open`:
  - `The application was opened successfully.`
- `reset`:
  - `The application has just been reset.`
- `add-account -t dec`:
  - `Account <generated-address> added (Dec).`
- `send`:
  - `Message sent from <sender> to <receiver>. Subject: <subject>`
- `sync-folder -f Inbox`:
  - `Folder 'Inbox' for account <account> synchronized.`

## Normative rules

- Treat `Normative command patterns for agents` and `Normative stdin contracts` as normative for agent workflows.
- Put global launch options before `--` and put the startup command after `--`.
- Do not assume `open` creates a reusable session for future process launches.
- Synchronize the relevant folder before reading when the task requires newly arrived messages.
- Do not guess provider-specific folder names; call `list-folders` first.
- Use `-l` / `--limit` when predictable payload size matters.
- Do not pass account secrets in command-line arguments when structured standard input is supported.

`eppie-console open` only opens the vault inside the current process.
It does **not** create a reusable session for future process launches.

## Normative command patterns for agents

Use this section as the single source of truth for agent command lines. Unless text output is explicitly required, all agent examples below use `--output=json`.

| Task | Canonical command |
| --- | --- |
| Initialize a vault | `--non-interactive=true --output=json -- init` |
| List accounts | `--non-interactive=true --unlock-password-stdin=true --output=json -- list-accounts` |
| List folders | `--non-interactive=true --unlock-password-stdin=true --output=json -- list-folders -a <account>` |
| Show all messages | `--non-interactive=true --unlock-password-stdin=true --output=json -- show-all-messages -s 10 -l 10` |
| Show one message | `--non-interactive=true --unlock-password-stdin=true --output=json -- show-message -a <account> -f <folder> -i <id> -k <pk>` |
| Delete one message | `--non-interactive=true --unlock-password-stdin=true --output=json -- delete-message -a <account> -f <folder> -i <id> -k <pk>` |
| List contacts | `--non-interactive=true --unlock-password-stdin=true --output=json -- list-contacts -s 10 -l 10` |
| Show contact messages | `--non-interactive=true --unlock-password-stdin=true --output=json -- show-contact-messages -c <contact> -s 10 -l 10` |
| Show folder messages | `--non-interactive=true --unlock-password-stdin=true --output=json -- show-folder-messages -a <account> -f <folder> -s 10 -l 10` |
| Sync a folder | `--non-interactive=true --unlock-password-stdin=true --output=json -- sync-folder -a <account> -f <folder>` |
| Send a message | `--non-interactive=true --unlock-password-stdin=true --output=json -- send -s <sender> -r <receiver> -t "<subject>"` |
| Reset local data | `--non-interactive=true --assume-yes=true --output=json -- reset` |
| Add a DEC account | `--non-interactive=true --unlock-password-stdin=true --output=json -- add-account -t dec` |
| Add a regular IMAP/SMTP account | `--non-interactive=true --unlock-password-stdin=true --output=json -- add-account -t email --input-json-stdin` |
| Add a Proton Mail account | `--non-interactive=true --unlock-password-stdin=true --output=json -- add-account -t proton --input-json-stdin` |

## Normative stdin contracts

Provide `stdin` exactly in the documented order. Unless a command explicitly reads until end-of-stream, stop after the documented input has been written.

| Command | Exact `stdin` contract | EOF required |
| --- | --- | --- |
| `--non-interactive=true --output=json -- init` | line 1: new vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- list-accounts` | line 1: vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- list-folders -a <account>` | line 1: vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- show-all-messages -s <page-size> -l <limit>` | line 1: vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- show-message -a <account> -f <folder> -i <id> -k <pk>` | line 1: vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- delete-message -a <account> -f <folder> -i <id> -k <pk>` | line 1: vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- list-contacts -s <page-size> -l <limit>` | line 1: vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- show-contact-messages -c <contact> -s <page-size> -l <limit>` | line 1: vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- show-folder-messages -a <account> -f <folder> -s <page-size> -l <limit>` | line 1: vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- sync-folder -a <account> -f <folder>` | line 1: vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- send -s <sender> -r <receiver> -t "<subject>"` | line 1: vault password; line 2 and later: message body; then close `stdin` | yes |
| `--non-interactive=true --assume-yes=true --output=json -- reset` | no `stdin` | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- add-account -t dec` | line 1: vault password | no |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- add-account -t email --input-json-stdin` | line 1: vault password; remaining bytes: one JSON object | yes |
| `--non-interactive=true --unlock-password-stdin=true --output=json -- add-account -t proton --input-json-stdin` | line 1: vault password; remaining bytes: one JSON object | yes |

### Command summary

| Command group | Needs existing vault | Use `--unlock-password-stdin=true` | Prefer `--output=json` | Notes |
| --- | --- | --- | --- | --- |
| `init` | no | no | yes for agent workflows | writes a new local vault password from `stdin` |
| `reset` | no | no | yes | destructive; also use `--assume-yes=true` |
| `list-accounts`, `list-folders` | yes | yes | yes | inspect vault content |
| `show-all-messages`, `show-message`, `show-folder-messages`, `show-contact-messages` | yes | yes | yes | use `-l` when payload size matters |
| `sync-folder` | yes | yes | yes | call before reading when fresh messages are required |
| `send` | yes | yes | yes | password first in `stdin`, then body until EOF |
| `add-account -t dec` | yes | yes | yes | simple vault-backed account creation |
| `add-account -t email`, `add-account -t proton` | yes | yes | yes | use `--input-json-stdin`; do not pass secrets in arguments |

### Avoid these mistakes

- Do not use `open` in a non-interactive workflow.
- Do not guess provider-specific folder names; call `list-folders` first.
- Do not rely only on process exit code when JSON output is available.
- Do not omit `-l` when an agent needs a predictable maximum payload size.
- Do not pass secrets in command-line arguments when structured standard input is supported.

## Normative execution policy for autonomous agents

### Output handling
- Follow the `Normative defaults for agents` defaults unless the task explicitly requires otherwise.
- Parse `type`, `code`, `data`, `meta`, and `message` from the normalized envelope.
- Do not rely only on process exit code when structured output is available.
- Treat `warning` and `error` responses as non-success outcomes even when the process exits cleanly.

### Standard input handling
- Follow `Normative stdin contracts` exactly.
- For `send`, close `stdin` after the last body line.
- For commands using `--input-json-stdin`, pass the password first when required, then the JSON payload.
- Do not prepend labels, prompts, or extra blank lines to the documented `stdin` contract.

### Working directory handling
- Use one consistent working directory for related commands that operate on the same local vault.
- Use an isolated working directory when the run is disposable or destructive.

### Account identifier handling
- For agent workflows, pass the account address from `list-accounts` `data[].address` to `-a`.
- Do not assume the numeric `id` is accepted interchangeably by all commands.
- Re-read the current address from `list-accounts` when a workflow depends on a newly created account.

### Pagination handling
- Use both `-s` / `--page-size` and `-l` / `--limit` in agent workflows when payload size must be predictable.
- Treat `-s` as page size only. Treat `-l` as the total maximum number of records returned by the command.
- If `-l` is omitted, paged read commands return up to 20 records by default.
- Use `meta.returned` to confirm how many records were actually returned.
- Use `meta.hasMore` to decide whether another read with a higher `-l` or a narrower filter is needed.
- Do not assume provider folders or message volume are small enough to omit `-l`.

## Reference: decision guide

Use `Normative command patterns for agents` for the exact command line. This guide is only for choosing the next command.

- inspect available accounts → `list-accounts`
- inspect available folders for an account → `list-folders`
- inspect recent messages across folders → sync the relevant folders when new messages are required, then use `show-all-messages`
- inspect messages in a specific folder → `list-folders`, then `sync-folder`, then `show-folder-messages` when new messages are required
- inspect one message → `show-message`
- delete one message → `delete-message`
- inspect contacts → `list-contacts`
- inspect messages for one contact → `show-contact-messages`
- send a message → `send`
- sync one folder → `list-folders`, then `sync-folder`
- initialize a vault → `init`
- reset local data → `reset`

## Reference: end-to-end agent scenarios

This section is informative. Use `Normative command patterns for agents` for the exact command line and `Normative stdin contracts` for the exact `stdin` shape.

### Initialize a new vault, add an account, then verify it

Use this flow when the working directory does not yet contain the required local vault.

1. initialize the vault with `init`
2. add the required account with `add-account`
3. verify the created account with `list-accounts`
4. use the returned `data[].address` as `<account>` in later commands

Typical sequences:
- DEC account: `init` → `add-account -t dec` → `list-accounts`
- regular IMAP/SMTP account: `init` → `add-account -t email` → `list-accounts`
- Proton Mail account: `init` → `add-account -t proton` → `list-accounts`

Agent notes:
- keep one consistent working directory across the whole sequence so all commands operate on the same local vault
- for `add-account -t email` and `add-account -t proton`, provide the structured payload through standard input after the vault password as documented in `Normative stdin contracts`
- after account creation, re-read the current address from `list-accounts` instead of assuming another identifier format

### Read the latest message from a specific folder

Use this flow when the task requires a concrete folder such as inbox or sent mail and the messages may have changed since the last sync.

1. inspect accounts with `list-accounts`
2. inspect folders for the chosen account with `list-folders`
3. choose the correct folder name from `data[].fullName` or `data[].roles`
4. synchronize that folder with `sync-folder`
5. read a bounded message list with `show-folder-messages`
6. open one returned message with `show-message` using its `id` and `pk`

Typical sequence:
- `list-accounts` → `list-folders` → `sync-folder` → `show-folder-messages` → `show-message`

Agent notes:
- do not guess the folder name; use the `fullName` returned by `list-folders`
- use `-s` and `-l` on `show-folder-messages` when predictable payload size matters
- when `meta.hasMore` is `true`, treat the result as partial and increase `-l` only if the task requires a larger set

### Send a message from an existing account

Use this flow when the local vault already contains the sender account and the task is to deliver one message deterministically.

1. inspect accounts with `list-accounts`
2. choose the sender address from `data[].address`
3. call `send` with the sender, receiver, and subject
4. pass the vault password on the first `stdin` line
5. pass the message body starting from line 2, then close `stdin`

Typical sequence:
- `list-accounts` → `send`

Agent notes:
- if the sender is unknown or the workflow depends on a newly created account, refresh the account list before sending
- in `--non-interactive=true` mode, `send` reads the body until end-of-stream, so the agent should close `stdin` after the last body line
- prefer `--output=json` and verify the `messageSent` status response instead of relying only on the process exit code

## Reference: command-specific notes and examples

The canonical command lines are defined in `Normative command patterns for agents`, and the exact inputs are defined in `Normative stdin contracts`. This section keeps only command-specific notes, result shapes, and examples that are easy to reference during agent execution.

### Init local vault
Notes:
- writes a new local vault password from `stdin`

### Show all messages
Notes:
- `-s` / `--page-size` controls only the page size
- `-l` / `--limit` caps the total number of returned records and should be used by agents to keep payload size predictable
- if `-l` is omitted, paged read commands return up to 20 records by default
- message items use the same address shape as `show-message`: `to` and `from` are arrays
- paged result metadata can include `returned` and `hasMore`
- agents should check `meta.hasMore` before assuming the returned list is complete

### List folders
Expected result shape:
- `{"type":"result","code":"folders","data":[{"fullName":"Inbox","unreadCount":0,"totalCount":0,"roles":["inbox"]}],"meta":{"account":"<account>"}}`

Notes:
- `<account>` should be the account address from `list-accounts` `data[].address`
- use this command before `show-folder-messages` or `sync-folder` instead of guessing provider-specific folder names
- Proton may expose names such as `All Sent`; rely on the returned `fullName`
- use `roles` when you need a machine-readable way to find folders such as inbox or sent mail

### Delete one message
Notes:
- when called for a message outside `Trash`, the command moves the message to `Trash`
- when called for a message already in `Trash`, the command deletes it permanently

### Show contact messages
Notes:
- paged result metadata can include `returned` and `hasMore`

### Show folder messages
Notes:
- paged result metadata can include `returned` and `hasMore`

### Sync folder
Expected result shape:
- `{"type":"status","code":"folderSynced","data":{"account":"<account>","folder":"Inbox"}}`

### Send message
Examples:
- `vault password`
- `Hello from automation`
- `Second body line`
- close `stdin`

Notes:
- in `--non-interactive=true` mode, `send` reads the message body until end-of-stream
- JSON success shape: `{"type":"status","code":"messageSent","data":{"subject":"<subject>","to":"<receiver>","from":"<sender>"}}`

PowerShell example with the command line and exact `stdin` in one block:

```powershell
@"
vault password
Hello from automation
Second body line
"@ | .\eppie-console --non-interactive=true --unlock-password-stdin=true --output=json -- send -s sender@example.com -r receiver@example.com -t "Hello from automation"
```

Linux / bash example with the command line and exact `stdin` in one block:

```bash
cat <<'EOF_INPUT' | ./eppie-console --non-interactive=true --unlock-password-stdin=true --output=json -- send -s sender@example.com -r receiver@example.com -t "Hello from automation"
vault password
Hello from automation
Second body line
EOF_INPUT
```

Notes:
- on Linux and macOS, use `./eppie-console` after extracting the archive and making sure the file is executable.

### Open local vault
Use `open` only in interactive mode when the agent is already inside a REPL session and must open the local vault in that same process.

Notes:
- do not use `open` as part of the non-interactive agent workflow

### Reset local data
Notes:
- `reset` is a destructive command and should be called with `--assume-yes=true` in automation or other non-interactive scripts.

### Add DEC account
Expected result shape:
- `{"type":"result","code":"accountAdded","data":{"address":"<generated-address>","accountType":"Dec"},"meta":null}`

### Add regular IMAP/SMTP account
Examples:

JSON object:

```json
{
  "email": "user@example.com",
  "accountPassword": "account password",
  "imapServer": "imap.example.com",
  "imapPort": 993,
  "smtpServer": "smtp.example.com",
  "smtpPort": 465
}
```

`stdin` shape:
- first line: `vault password`
- remaining bytes:

```json
{"email":"user@example.com","accountPassword":"account password","imapServer":"imap.example.com","imapPort":993,"smtpServer":"smtp.example.com","smtpPort":465}
```

Notes:
- use this mode for regular IMAP/SMTP providers when browser-based OAuth is not needed
- do not pass account secrets in command-line arguments
- required structured properties are `email`, `accountPassword`, `imapServer`, `imapPort`, `smtpServer`, and `smtpPort`
- invalid structured input returns one of these machine-readable errors:
  - `structuredStandardInputInvalidJson`
  - `structuredStandardInputMissingProperty`

### Add Proton Mail account
Examples:

JSON object:

```json
{
  "email": "user@proton.me",
  "accountPassword": "account password",
  "mailboxPassword": "mailbox password",
  "twoFactorCode": "123456"
}
```

`stdin` shape:
- first line: `vault password`
- remaining bytes:

```json
{"email":"user@proton.me","accountPassword":"account password","mailboxPassword":"mailbox password"}
```

Notes:
- do not pass Proton secrets in command-line arguments
- `email` and `accountPassword` are required in structured input
- `mailboxPassword` is required only if the Proton flow asks for it
- `twoFactorCode` is required only if the Proton flow asks for it
- if the mailbox password is the same as the account password, repeat the same value in `mailboxPassword`
- invalid structured input returns one of these machine-readable errors:
  - `structuredStandardInputInvalidJson`
  - `structuredStandardInputMissingProperty`

## Reference: recommended agent workflow

1. Start from the defaults in `Normative defaults for agents`.
2. Choose the exact command line from `Normative command patterns for agents`.
3. Provide `stdin` in the exact shape defined in `Normative stdin contracts`.
4. Use the account address from `list-accounts` `data[].address` for `-a`.
5. Use an isolated working directory when the run is disposable or destructive.
6. For message reading:
   - start with `list-folders` if the next step requires a specific folder name,
   - synchronize the relevant folder before reading when you need newly arrived messages,
   - then use `show-all-messages` when you need recent messages across all folders,
   - then call `show-message` or `delete-message` with the returned `id` and `pk`.
7. In `--non-interactive=true` mode text output stops after the first page instead of prompting.
8. For common task chains, use `Reference: end-to-end agent scenarios` as a quick reference.

## Reference: known limitations

### Some commands still require explicit non-interactive inputs
`--non-interactive=true` suppresses interactive prompts, but it does not invent missing data.

Commands that normally ask follow-up questions still need explicit arguments or `stdin` data.
The main examples are already covered above:
- `send` reads the message body until end-of-stream in `--non-interactive=true` mode
- `add-account -t email` and `add-account -t proton` should use `--input-json-stdin`
- destructive commands such as `reset` still need `--assume-yes=true`
- paged read commands still default to 20 records when `-l` is omitted

## Normative error handling

For agent automation, prefer deterministic handling over implicit retries.

### Interpret the normalized envelope

When `--output=json` is enabled, handle responses by `type` first:

| `type` | Meaning | Agent action |
| --- | --- | --- |
| `result` | command returned data | parse `data` and `meta` |
| `status` | command completed successfully without a list-style result | read `data` when present |
| `warning` | handled problem or non-success condition | inspect `code`; do not assume success; stop unless the workflow explicitly defines a recovery step |
| `error` | handled failure | inspect `code`, `message`, and `data`; stop unless the input can be corrected deterministically |

### Common machine-readable codes

| `code` | Meaning | Typical agent response |
| --- | --- | --- |
| `invalidPassword` | vault password was rejected | stop; do not retry automatically with the same password |
| `structuredStandardInputInvalidJson` | structured payload is not valid JSON | fix serialization and retry once with corrected JSON |
| `structuredStandardInputMissingProperty` | required JSON property is missing or empty | provide the missing property and retry once |
| `unhandledException` | command failed and returned exception details | inspect `data.exceptionType` and command context; do not retry blindly |

### Agent response rules

- Parse `type` first, then `code`.
- Do not treat `warning` as success.
- Do not retry `invalidPassword` automatically.
- Retry only when the failure is deterministic and local to the request, such as malformed JSON or a missing structured property.
- When retrying after `structuredStandardInputInvalidJson` or `structuredStandardInputMissingProperty`, change only the invalid input and keep the command line unchanged.
- For `unhandledException`, record the command, the parsed `code`, and `data.exceptionType` when present.
- When a paged read returns `meta.hasMore: true`, treat that as an incomplete result set rather than an error.

### Error-output examples

Invalid password example:
- `{"type":"warning","code":"invalidPassword","message":"Warning: Invalid password.","data":null}`

Unknown sender account example for `send`:
- `{"type":"error","code":"unhandledException","message":"An error has occurred: ...","data":{"exceptionType":"Tuvi.Core.Entities.AccountIsNotExistInDatabaseException"}}`

Invalid Proton structured input example:
- `{"type":"error","code":"structuredStandardInputInvalidJson","message":"Error: The remaining standard input for the 'add-account' command is not valid JSON.","data":{"commandName":"add-account"}}`

Missing Proton structured property example:
- `{"type":"error","code":"structuredStandardInputMissingProperty","message":"Error: The structured standard input for the 'add-account' command must contain a non-empty 'email' property.","data":{"commandName":"add-account","propertyName":"email"}}`

## Reference: contributing

Contributions are welcome.

Please open issues for bugs, UX problems, and feature ideas.
Pull requests on GitHub are also welcome.

Repository:
- https://github.com/Eppie-io/Eppie-CLI
