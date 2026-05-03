---
name: Multi-Agent Orchestrator
description: An autonomous loop that coordinates worker agents (Kilo, Aider, etc) with a dashboard to monitor the agents' activity. Best used with a powerful Orchestrator and cost-efficient workers.
dependencies:
  - headless-cli-agent (e.g. kilo-cli, aider)
  - typescript
  - ts-node
---

# FULL Claude Orchestrator Skill

This skill defines a COMPLETE, CLI-agnostic multi-agent orchestration system.

## Prerequisites & Recommendations
Before using this skill, ensure you have:
1. **A Headless Worker CLI**: Installed globally. This skill uses `kilo` (Kilo Code) by default, but it can easily orchestrate **Aider**, **OpenCode**, or any other CLI defined in the `scripts/spawn-agent.ts` file. **Important:** The CLI must be fully configured ahead of time (e.g., signed in, API keys set, default model selected). Because the agents run headlessly in the background, they will crash or hang if they encounter interactive setup prompts. Additionally, ensure your chosen CLI is configured to automatically index/load the project codebase as context, or that it has tools to autonomously search files.
2. **TypeScript & TS-Node**: Installed to execute the orchestration scripts.
3. **Claude Code CLI**: Installed and authenticated, as the background loop relies on `claude -p` for headless execution.

> **Architectural Recommendation:** 
> This skill is highly optimized for cost-efficiency without sacrificing quality. We strongly recommend configuring your **Claude Code CLI** to use a high-tier reasoning model (like Claude Opus 4.7) to act as the "brains" of the orchestrator loop. Meanwhile, you should configure your **Worker CLI** (Kilo/Aider) default to use API-efficient models (like DeepSeek v4 or Kimi) for the worker agents. This ensures world-class decision making while keeping the bulk coding loops extremely cheap and fast!

## 🔄 Swapping the Worker CLI (Aider, Claude, Codex, Gemini, OpenCode, etc.)
By default, `spawn-agent.ts` launches workers using Kilo Code (`kilo <prompt> --auto`). 
Because the orchestration architecture (worktrees + JSON files) is completely CLI-agnostic, you can use any other tool by simply appending the `--cli` argument in Phase 4 when you spawn the agent!
*   **For Aider**: Append `--cli aider` (runs `aider --message <prompt> --yes`)
*   **For Claude Code**: Append `--cli claude` (runs `claude -p <prompt>`)
*   **For OpenAI Codex CLI**: Append `--cli codex` (runs `codex --exec <prompt>`)
*   **For Gemini CLI**: Append `--cli gemini` (runs `gemini --prompt <prompt>`)
*   **For OpenCode**: Append `--cli opencode` (runs `opencode run <prompt>`)

The Orchestrator Loop will remember which CLI tool you spawned the agent with and will automatically use the exact same tool if it needs to respawn the agent after a rollback!

## Phase 1 — Task Evaluation & Decomposition
First, evaluate whether the user's overall task is suitable for multi-agent orchestration.
- **Do not use this skill** if the task is small, trivial, or requires tightly coupled sequential steps. Advise the user to let you handle it normally.
- **Proceed** if the task is large, complex, and can be safely split into non-overlapping boundaries (e.g., frontend vs backend, database vs UI).

If proceeding, break the work down into non-overlapping agent boundaries and prepare a mapping of agent names to their task descriptions.

## Phase 2 — Bootstrap
When starting a new orchestrated project, create the `coord/` directory at the project root and initialize these files.

**Important Path Resolution:** The scripts required for this workflow are located in the `scripts/` directory next to this `SKILL.md` file. Before running the commands below, determine the absolute path to this skill folder (e.g., if you are reading this from `~/Desktop/multi-agent-orchestrator/SKILL.md`, the path is `~/Desktop/multi-agent-orchestrator`).

```bash
npx ts-node <ABSOLUTE_PATH_TO_THIS_SKILL_FOLDER>/scripts/bootstrap.ts \
  --project "Your project description" \
  --chat-context "Compacted history and unspoken preferences" \
  --coord ./coord
```

### `coord/context.json`
Because the orchestrator loop runs in a detached Claude CLI session, it has **zero access** to your original chat history. **You must heavily compress all user preferences, architectural nuances, and conversational context into the `chat_context` field.**

You should also include the tasks you generated in Phase 1 under the `"tasks"` key.

```json
{
  "project": "<one-line description of the user's task>",
  "chat_context": "<heavily compacted summary of the original conversation and user preferences>",
  "requirements": ["<requirement 1>", "<requirement 2>"],
  "constraints": ["<constraint 1>", "<constraint 2>"],
  "created_at": "<ISO 8601 timestamp>",
  "tasks": {
    "agent-name": "description of the boundary"
  }
}
```

## Phase 3 — Prompt Generation
Use the `references/worker-prompt-template.md` to generate prompts for each agent.

## Phase 4 — Spawning Agents
For each agent:
1. Create a git worktree. If you are using Kilo Code, create it in `.kilocode/worktrees/` so it appears in the VS Code UI. If using Aider or another tool, use `.agents/worktrees/`:
   ```bash
   git worktree add <worktree-path>/<agent-name> -b <agent-name>
   ```
2. **Launch the agent in the background** using the `spawn-agent.ts` helper:
   ```bash
   echo "YOUR PROMPT HERE" > /tmp/prompt-<agent-name>.txt
   npx ts-node <ABSOLUTE_PATH_TO_THIS_SKILL_FOLDER>/scripts/spawn-agent.ts \
     --agent <agent-name> \
     --mode <mode> \
     --prompt-file /tmp/prompt-<agent-name>.txt \
     --coord ./coord \
     --cli <cli-name> # Optional: e.g. aider, claude. Defaults to kilo.
   ```

> **💡 Tip for Kilo Code Users:** Because the agents are physically spawned inside the `.kilocode/worktrees/` directory path by default, they will automatically appear in your **Kilo Code Agent Manager UI** inside VS Code! You can monitor the specific files they are editing in real-time natively in your IDE.

## Phase 5 — The Orchestrator Loop

To ensure the loop runs independently, launch it in the background and exit:

```bash
nohup npx ts-node <ABSOLUTE_PATH_TO_THIS_SKILL_FOLDER>/scripts/orchestrator-loop.ts --coord ./coord > coord/orchestrator-loop.out 2>&1 &
```

**Once the loop is started, your job as the starter session is done. You should politely inform the user that the orchestration loop is running in the background and exit.**

### Action Types

| Action | Effect |
|--------|--------|
| `end_agent` | Orchestrator loop sends SIGTERM to the process and marks it `"completed"`. |
| `restart_agent` | Orchestrator loop handles everything automatically: it kills the rogue process, runs `git reset --hard` (if `rollback` is `true`), and uses `spawn-agent.ts` to immediately respawn the agent with the new `instruction`. |

## Phase 6 — Review and Integration

When all worker agents finish, the `orchestrator-loop.ts` script will trigger a **macOS Desktop Notification** to alert the user and then automatically exit.

At this point, the user will return to Claude. They can either use their original chat window, or open a completely new chat window. They will give you a command like *"The agents are done. Please review and integrate their work."*

When you receive this instruction to perform the final integration, you should:
1. Identify the completed agent worktrees (look in both `.kilocode/worktrees/` and `.agents/worktrees/`).
2. Run `git diff main...<agent-name>` for each to review the code.
3. Provide a summary of the work to the user.
4. Once the user approves, perform the merge:
   ```bash
   git merge <agent-name>
   git worktree remove <worktree-path>/<agent-name>
   git branch -d <agent-name>
   ```
