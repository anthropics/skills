#!/usr/bin/env ts-node

import * as fs from "fs";
import * as path from "path";
import { execSync } from "child_process";

// ─── Types ───────────────────────────────────────────────────────────────────

interface Config {
  coordDir: string;
  pollIntervalMs: number;
  claudeModel: string;
  maxRetries: number;
  logFile: string;
}

interface Request {
  request_id: string;
  agent: string;
  type: "question" | "change" | "conflict" | "review_request";
  priority: "low" | "medium" | "high";
  content: string;
  status: "pending" | "resolved" | "rejected";
  created_at: string;
}

interface Decision {
  request_id: string;
  decision: string;
  reason: string;
  resolved_at: string;
}

interface AgentEntry {
  task: string;
  status: "running" | "completed" | "terminated" | "errored";
  worktree: string;
  kilo_mode: string;
  pid: number;
  started_at: string;
  last_heartbeat: string;
}

interface OrchestratorAction {
  type: "end_agent" | "restart_agent";
  agent: string;
  instruction?: string;
  rollback?: boolean;
}

interface OrchestratorResponse {
  approved: Array<{ request_id: string; decision: string; reason: string }>;
  rejected: Array<{ request_id: string; reason: string }>;
  actions: OrchestratorAction[];
}

interface ProjectContext {
  project: string;
  chat_context?: string;
  requirements: string[];
  constraints: string[];
  created_at: string;
  tasks?: Record<string, string>;
}

// ─── Utilities ───────────────────────────────────────────────────────────────

function sleep(ms: number) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function readJSON<T>(filePath: string): T {
  return JSON.parse(fs.readFileSync(filePath, "utf-8"));
}

function writeJSON<T>(filePath: string, data: T): void {
  fs.writeFileSync(filePath, JSON.stringify(data, null, 2) + "\n");
}

function appendLog(logFile: string, message: string): void {
  const timestamp = new Date().toISOString();
  const logMsg = `[${timestamp}] ${message}\n`;
  fs.appendFileSync(logFile, logMsg);
  console.log(logMsg.trim());
}

function killAgentProcess(pid: number, logFile: string) {
  if (pid) {
    try {
      process.kill(pid, "SIGTERM");
      appendLog(logFile, `Sent SIGTERM to agent process PID ${pid}.`);
    } catch (err: any) {
      if (err.code === "ESRCH") {
        appendLog(logFile, `Agent process PID ${pid} already exited.`);
      } else {
        appendLog(logFile, `Failed to kill agent PID ${pid}: ${err.message}`);
      }
    }
  }
}

// ─── Configuration ───────────────────────────────────────────────────────────

function parseArgs(): Config {
  const args = process.argv.slice(2);
  const config: Config = {
    coordDir: "./coord",
    pollIntervalMs: 5000,
    claudeModel: "claude-3-7-sonnet-20250219",
    maxRetries: 3,
    logFile: "coord/orchestrator.log",
  };

  for (let i = 0; i < args.length; i++) {
    if (args[i] === "--coord") config.coordDir = args[++i];
    if (args[i] === "--poll-interval") config.pollIntervalMs = parseInt(args[++i], 10);
  }

  return config;
}

function getPaths(coordDir: string) {
  return {
    requests: path.join(coordDir, "requests.json"),
    decisions: path.join(coordDir, "decisions.json"),
    context: path.join(coordDir, "context.json"),
    agents: path.join(coordDir, "agents.json"),
  };
}

// ─── Claude CLI Integration ──────────────────────────────────────────────────

function buildOrchestratorPrompt(
  requests: Request[],
  context: ProjectContext,
  decisions: Decision[],
  worktreeStates: Record<string, string>
): string {
  return `You are the system orchestrator for a multi-agent project using Kilo Code.

Worker agents are running as Kilo Code sessions, each in an isolated git worktree.
They communicate by writing requests to coord/requests.json.

## Project Context
${JSON.stringify(context, null, 2)}

## Existing Decisions (DO NOT contradict these)
${JSON.stringify(decisions, null, 2)}

## Agent Worktree States (Code Context)
Here is the current git status and diff for the agents that submitted requests. Use this code context to understand their progress and evaluate their requests:
${JSON.stringify(worktreeStates, null, 2)}

## New Requests from Kilo Agents
${JSON.stringify(requests, null, 2)}

## Your Responsibilities
- Maintain consistency across all Kilo agent sessions
- Resolve requests without contradicting existing decisions
- Prevent conflicts between agents working in parallel worktrees
- Prefer minimal disruption to running Kilo sessions
- Reject unclear requests — ask for clarification rather than guessing
- **IMPORTANT**: Every request you process MUST be explicitly included in either the \`approved\` or \`rejected\` array. Even if you issue an action (like \`end_agent\`), you MUST STILL approve the request that triggered it so it is marked as resolved.

## Response Format
Return ONLY valid JSON matching this exact structure (no markdown, no explanation):
{
  "approved": [
    {
      "request_id": "...",
      "decision": "clear statement of what was decided",
      "reason": "why this decision was made"
    }
  ],
  "rejected": [
    {
      "request_id": "...",
      "reason": "why this was rejected"
    }
  ],
  "actions": [
    {
      "type": "end_agent | restart_agent",
      "agent": "agent-name",
      "instruction": "optional — new instructions for the Kilo session",
      "rollback": false
    }
  ]
}
`;
}

function callClaude(prompt: string, model: string, maxRetries: number, logFile: string): OrchestratorResponse | null {
  const escapedPrompt = prompt.replace(/"/g, '\\"').replace(/\$/g, '\\$');
  const claudeCmd = `claude -p "${escapedPrompt}"`;

  for (let attempt = 1; attempt <= maxRetries; attempt++) {
    try {
      appendLog(logFile, `Calling Claude (Attempt ${attempt}/${maxRetries})...`);
      const stdout = execSync(claudeCmd, { encoding: "utf-8", maxBuffer: 1024 * 1024 * 10 });

      const match = stdout.match(/\{[\s\S]*\}/);
      if (!match) throw new Error("No JSON object found in Claude output.");

      const parsed = JSON.parse(match[0]);
      appendLog(logFile, `Claude call succeeded.`);
      return parsed;
    } catch (err: any) {
      appendLog(logFile, `Claude call failed: ${err.message}`);
      if (attempt === maxRetries) {
        appendLog(logFile, "Max retries reached. Returning null.");
        return null;
      }
    }
  }
  return null;
}

// ─── Loop Execution ──────────────────────────────────────────────────────────

async function runLoop() {
  const config = parseArgs();
  const paths = getPaths(config.coordDir);

  if (!fs.existsSync(paths.requests) || !fs.existsSync(paths.decisions) || !fs.existsSync(paths.context)) {
    console.error("Missing coordination files. Run bootstrap first.");
    process.exit(1);
  }

  appendLog(config.logFile, `Starting Orchestrator Loop (Polling every ${config.pollIntervalMs}ms)`);

  // Launch the live dashboard in a new macOS Terminal
  try {
    const dashboardPath = path.join(__dirname, "dashboard.ts");
    const scriptStr = `tell application "Terminal" to do script "cd '${process.cwd()}' && npx ts-node '${dashboardPath}' --coord '${config.coordDir}'"`;
    execSync(`osascript -e '${scriptStr}'`);
    appendLog(config.logFile, "Launched dashboard terminal.");
  } catch (e: any) {
    appendLog(config.logFile, `Failed to launch dashboard: ${e.message}`);
  }

  while (true) {
    try {
      if (fs.existsSync(path.join(config.coordDir, "abort.flag"))) {
        appendLog(config.logFile, "🛑 ABORT SIGNAL RECEIVED from dashboard. Terminating all agents...");
        const agents = readJSON<Record<string, AgentEntry>>(paths.agents);
        for (const name in agents) {
          if (agents[name].status === "running") {
            killAgentProcess(agents[name].pid, config.logFile);
            const worktree = agents[name].worktree;
            if (fs.existsSync(worktree)) {
              appendLog(config.logFile, `Resetting worktree ${worktree}...`);
              try { execSync(`git reset --hard HEAD && git clean -fd`, { cwd: worktree }); } catch(e) {}
            }
            agents[name].status = "errored";
            agents[name].task = "ABORTED BY USER";
          }
        }
        writeJSON(paths.agents, agents);
        appendLog(config.logFile, "All agents terminated and reset. Orchestrator loop aborting.");
        try { fs.unlinkSync(path.join(config.coordDir, "abort.flag")); } catch (e) {}
        break;
      }

      // Check for crashed agents (e.g. network failures)
      const agentsForCheck = readJSON<Record<string, AgentEntry>>(paths.agents);
      let agentsChanged = false;
      for (const name in agentsForCheck) {
        if (agentsForCheck[name].status === "running") {
          try {
            process.kill(agentsForCheck[name].pid, 0); // 0 signal tests if process is alive
          } catch (e) {
            agentsForCheck[name].status = "errored";
            agentsChanged = true;
            appendLog(config.logFile, `⚠️ Agent ${name} (PID ${agentsForCheck[name].pid}) died unexpectedly!`);
          }
        }
      }
      if (agentsChanged) writeJSON(paths.agents, agentsForCheck);

      const requests = readJSON<Request[]>(paths.requests);
      const pending = requests.filter((p) => p.status === "pending");

      if (pending.length > 0) {
        appendLog(config.logFile, `Found ${pending.length} pending requests.`);

        const context = readJSON<ProjectContext>(paths.context);
        const decisions = readJSON<Decision[]>(paths.decisions);
        const agents = readJSON<Record<string, AgentEntry>>(paths.agents);

        const worktreeStates: Record<string, string> = {};
        for (const req of pending) {
          if (!worktreeStates[req.agent] && agents[req.agent]) {
            const worktree = agents[req.agent].worktree;
            if (fs.existsSync(worktree)) {
              try {
                execSync('git add -A', { cwd: worktree });
                const status = execSync('git status -s', { cwd: worktree, encoding: 'utf-8' });
                const diff = execSync('git diff --cached', { cwd: worktree, encoding: 'utf-8' });
                worktreeStates[req.agent] = `STATUS:\n${status}\n\nDIFF:\n${diff.slice(0, 10000)}`;
              } catch (err: any) {
                worktreeStates[req.agent] = `Failed to read worktree state: ${err.message}`;
              }
            }
          }
        }

        const prompt = buildOrchestratorPrompt(pending, context, decisions, worktreeStates);
        const response = callClaude(prompt, config.claudeModel, config.maxRetries, config.logFile);

        if (!response) {
          appendLog(config.logFile, "Skipping cycle due to Claude failure.");
        } else {
          // Process Approved
          for (const approved of response.approved || []) {
            const req = requests.find((p) => p.request_id === approved.request_id);
            if (req) {
              req.status = "resolved";
              decisions.push({
                request_id: approved.request_id,
                decision: approved.decision,
                reason: approved.reason,
                resolved_at: new Date().toISOString(),
              });
              appendLog(config.logFile, `Approved Request ${approved.request_id}: ${approved.decision}`);
            }
          }

          // Process Rejected
          for (const rejected of response.rejected || []) {
            const req = requests.find((p) => p.request_id === rejected.request_id);
            if (req) {
              req.status = "rejected";
              appendLog(config.logFile, `Rejected Request ${rejected.request_id}: ${rejected.reason}`);
            }
          }

          // Process Actions
          for (const action of response.actions || []) {
            switch (action.type) {
              case "end_agent": {
                if (agents[action.agent]) {
                  killAgentProcess(agents[action.agent].pid, config.logFile);
                  agents[action.agent].status = "completed";
                  agents[action.agent].last_heartbeat = new Date().toISOString();
                  appendLog(config.logFile, `Agent ${action.agent} completed successfully.`);
                }
                break;
              }
              case "restart_agent": {
                if (agents[action.agent]) {
                  const worktree = agents[action.agent].worktree;
                  const mode = agents[action.agent].kilo_mode;
                  killAgentProcess(agents[action.agent].pid, config.logFile);
                  
                  if (action.rollback && fs.existsSync(worktree)) {
                    appendLog(config.logFile, `Rolling back worktree ${worktree}...`);
                    try {
                      execSync(`git reset --hard HEAD && git clean -fd`, { cwd: worktree });
                    } catch (err: any) {
                      appendLog(config.logFile, `Rollback failed: ${err.message}`);
                    }
                  }
                  
                  if (action.instruction) {
                    agents[action.agent].task = action.instruction;
                    const promptFile = path.join(require("os").tmpdir(), `prompt-${action.agent}-${Date.now()}.txt`);
                    fs.writeFileSync(promptFile, action.instruction, "utf-8");
                    
                    const cliTool = agents[action.agent].cli || "kilo";
                    appendLog(config.logFile, `Respawning agent ${action.agent} using ${cliTool}...`);
                    try {
                      execSync(`npx ts-node ${path.join(__dirname, "spawn-agent.ts")} --agent ${action.agent} --mode ${mode} --prompt-file "${promptFile}" --coord "${path.dirname(paths.agents)}" --cli ${cliTool}`);
                    } catch (err: any) {
                      appendLog(config.logFile, `Failed to respawn agent: ${err.message}`);
                    }
                    try { fs.unlinkSync(promptFile); } catch {}
                  } else {
                    agents[action.agent].status = "terminated";
                    appendLog(config.logFile, `Agent ${action.agent} terminated.`);
                  }
                }
                break;
              }
            }
          }

          writeJSON(paths.requests, requests);
          writeJSON(paths.decisions, decisions);
          writeJSON(paths.agents, agents);
        }
      } else {
        const agents = readJSON<Record<string, AgentEntry>>(paths.agents);
        const agentEntries = Object.values(agents);
        const allWorkersDone = agentEntries.length > 0 &&
          agentEntries.every(
            (a) => a.status === "completed" || a.status === "terminated" || a.status === "errored"
          );

        if (allWorkersDone) {
          appendLog(config.logFile, "All worker agents completed. Triggering macOS notification...");
          try {
            execSync(`osascript -e 'display notification "All Kilo agents have completed their tasks. Please return to your Claude session for the final review." with title "Kilo Orchestrator"'`);
          } catch (err: any) {
            appendLog(config.logFile, `Failed to send notification: ${err.message}`);
          }
          appendLog(config.logFile, "Orchestrator loop ending.");
          break;
        }
      }

      await sleep(config.pollIntervalMs);
    } catch (error: any) {
      appendLog(config.logFile, `Loop Error: ${error.message}`);
      await sleep(config.pollIntervalMs);
    }
  }
}

runLoop();
