#!/usr/bin/env ts-node

/**
 * Spawns a Kilo Code agent in the background and registers it in coord/agents.json
 */

import { spawn } from "child_process";
import * as fs from "fs";
import * as path from "path";

function parseArgs() {
  const args = process.argv.slice(2);
  const config = {
    agent: "",
    mode: "coder",
    promptFile: "",
    coordDir: "./coord",
    cli: "kilo",
  };

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case "--agent":
        config.agent = args[++i];
        break;
      case "--mode":
        config.mode = args[++i];
        break;
      case "--prompt-file":
        config.promptFile = args[++i];
        break;
      case "--coord":
        config.coordDir = args[++i];
        break;
      case "--cli":
        config.cli = args[++i];
        break;
    }
  }

  if (!config.agent || !config.promptFile) {
    console.error("Error: --agent and --prompt-file are required");
    process.exit(1);
  }

  return config;
}

function spawnAgent() {
  const config = parseArgs();
  const worktree = `.kilocode/worktrees/${config.agent}`;

  if (!fs.existsSync(worktree)) {
    console.error(`Error: Worktree ${worktree} does not exist. Run 'git worktree add ${worktree} -b ${config.agent}' first.`);
    process.exit(1);
  }

  const prompt = fs.readFileSync(config.promptFile, "utf-8");
  const logFile = `kilo-${config.agent}.log`;

  // Spawn the kilo CLI in the background
  // Build command based on selected CLI tool
  let cmd = "kilo";
  let cmdArgs = [prompt, "--mode", config.mode, "--auto"];

  if (config.cli === "aider") {
    cmd = "aider";
    cmdArgs = ["--message", prompt, "--yes"];
  } else if (config.cli === "claude") {
    cmd = "claude";
    cmdArgs = ["-p", prompt];
  }

  const child = spawn(cmd, cmdArgs, {
    detached: true,
    stdio: ["ignore", out, err],
    cwd: worktree,
  });

  child.unref(); // Allow the parent script to exit independently

  console.log(`✓ Spawned Kilo agent '${config.agent}' in background (PID: ${child.pid})`);
  console.log(`✓ Logging output to ${logFile}`);

  // Update agents.json
  const agentsFile = path.join(config.coordDir, "agents.json");
  let agents: any = {};
  if (fs.existsSync(agentsFile)) {
    agents = JSON.parse(fs.readFileSync(agentsFile, "utf-8"));
  }

  agents[config.agent] = {
    task: "Initial prompt",
    status: "running",
    worktree: worktree,
    cli: config.cli,
    kilo_mode: config.mode,
    pid: child.pid,
    started_at: new Date().toISOString(),
    last_heartbeat: new Date().toISOString(),
  };

  fs.writeFileSync(agentsFile, JSON.stringify(agents, null, 2) + "\n");
  console.log(`✓ Registered agent in ${agentsFile}`);
}

spawnAgent();
