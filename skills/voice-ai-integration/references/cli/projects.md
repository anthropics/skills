# Agora CLI Projects

Verified against Agora CLI `0.1.3`.

## Core Workflow

Use this sequence for most CLI project tasks:

```bash
agora login
agora project create my-agent-demo --feature rtc --feature rtm --feature convoai
agora project use my-agent-demo
agora project env
agora project feature list
```

## Project Commands

### Create

```bash
agora project create <name> [--region global|cn] [--type general|voice-agent|chat|rtc] [--template voice-agent] [--feature rtc|rtm|convoai]
```

For agent guidance, prefer explicit `--feature` flags because they match the later `project feature` workflow.

### List

```bash
agora project list [--page N] [--page-size N] [--keyword <text>]
```

Use this when the user needs to discover a project ID or exact project name.

### Select Current Project

```bash
agora project use <project>
```

`<project>` can be a project ID or exact project name.

After `project use`, commands like `project show`, `project feature list`, and `project doctor` can run without repeating the project argument.

### Show One Project

```bash
agora project show [project]
agora project show --json
```

This is the quickest way to inspect App ID, App Certificate, region, sign key, and token-enabled status for the current project.

Use `project show --json` for project metadata inspection.

If the user wants exported env vars or a dotenv workflow, route to [env.md](env.md) and use:

```bash
agora project env
agora project env --json
agora project env write
```

## Feature Commands

Valid verified feature names in `0.1.3`:

- `rtc`
- `rtm`
- `convoai`

Commands:

```bash
agora project feature list [project]
agora project feature status <feature> [project]
agora project feature enable <feature> [project]
```

Most ConvoAI onboarding preparation starts with:

```bash
agora project feature enable convoai
```

## Current-Project Context

If the user omits `[project]`, the CLI uses the locally selected project context.

If no project is selected, the verified recovery is:

```bash
agora project use <project>
```

or rerun the command with a project argument.

## Things Not to Hallucinate

- Do not invent `agora project delete`.
- Do not invent `agora project feature disable`.
- Do not invent ConvoAI-specific nested groups under `agora project`.
