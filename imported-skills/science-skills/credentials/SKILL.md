---
name: credentials
description: >-
  Instructions for handling API keys and credentials safely, verifying their
  presence, and prompting the user to add them if missing using a safe protocol.
---

# Safe Credentials Protocol

Many skills require API keys or other credentials to function or to access
higher rate limits. This skill defines the standard safe credentials protocol
for verifying and prompting for these credentials without leaking sensitive keys
into the agent context or the conversation history.

## Safe Verification (No Leaks)

As soon as a skill that requires a credential or API key looks relevant to the
user's request, you **MUST** immediately verify if the credential is present in
the `.env` file (typically located in your home directory `~/.env` or the
project root) — **before doing any other work** for that skill.

**CRITICAL**: You must verify the presence of the credential *without* printing
its value to the terminal or reading it into your context.

### How to verify:

Use `grep` in quiet and suppress-errors mode (`-sq`) to check if the variable is
defined in `~/.env`. The `-s` flag ensures the command works cleanly even if
`~/.env` does not exist yet.

```bash
grep -sq "^CREDENTIAL_NAME=" ~/.env
```

Replace `CREDENTIAL_NAME` with the actual credential name required by the
calling skill (e.g., `ALPHAGENOME_API_KEY` or `USER_EMAIL`).

-   If the command **succeeds** (exit code 0), the credential is present. You
    can proceed.
-   If the command **fails** (any non-zero exit code — whether the credential is
    missing or the `.env` file does not exist yet), the credential is missing.
    You **MUST IMMEDIATELY** stop and prompt the user to add it using the
    instructions in
    [Prompting the User to Add Credentials](#prompting-the-user-to-add-credentials)
    before attempting to run any scripts or tools. Do not conclude the turn by
    simply stating that the key is missing.

> [!CRITICAL] If verification fails (any non-zero exit code), you **MUST NOT**
> attempt to execute any tools or scripts from the calling skill, nor should you
> conclude the turn by simply reporting the missing key. You **MUST
> IMMEDIATELY** generate the appropriate terminal command from the templates
> below and prompt the user to run it. The template command will create the
> `.env` file if it does not already exist.

**NEVER** run `cat ~/.env`, `grep "VAR" ~/.env` (without `-q`), `echo $VAR`, or
`printenv` to check for credentials.

## Prompting the User to Add Credentials

If a credential is missing, do **NOT** ask the user to paste it into the chat.
This would leak the value into the agent's context and the conversation history.

Instead, you **MUST** generate a specific command for the user to run in their
terminal by replacing the placeholders in one of the templates below.

**CRITICAL**: Before presenting the command to the user, you **MUST** replace:

-   `CREDENTIAL_NAME` with the actual variable name needed (e.g.,
    `ALPHAGENOME_API_KEY`, `USER_EMAIL`).
-   `ENV_FILE` with the resolved literal path to the `.env` file (usually
    `~/.env`).

### Template

All credentials are treated as sensitive. The `read -s` flag hides the user's
typing. You **MUST** inform the user that their typing will be hidden.

**CRITICAL**: When requesting a credential, you **MUST** also provide the user
with the appropriate registration link or instructions provided by the calling
skill so they know how to obtain the value if they do not have one.

```bash
printf "Enter CREDENTIAL_NAME (typing hidden): " && read -s val && echo && echo "CREDENTIAL_NAME=$val" >> "ENV_FILE" && echo "Saved."
```

## Running scripts requiring credentials

All helper scripts inside the calling skills load these credentials
automatically from the `.env` file using `dotenv`.

**You do NOT need to** manually read the keys, export them to the shell
environment, or pass them as CLI arguments, when calling the helper scripts that
require them. As long as you have verified the key is present in `.env` using
the safe protocol above, simply run the script directly — the script will load
the credential automatically.
