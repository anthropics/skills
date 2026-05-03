#!/usr/bin/env ts-node

import * as fs from "fs";
import * as path from "path";

const coordDir = process.argv[2] === "--coord" ? process.argv[3] : "./coord";
const agentsFile = path.join(coordDir, "agents.json");
const requestsFile = path.join(coordDir, "requests.json");

function clearScreen() {
  process.stdout.write("\x1Bc");
}

function handleAbort() {
  console.log("\n🛑 Dashboard closed. Sending abort signal to Orchestrator...");
  try {
    fs.writeFileSync(path.join(coordDir, "abort.flag"), "true");
  } catch (e) {}
  process.exit(0);
}

process.on("SIGINT", handleAbort);
process.on("SIGHUP", handleAbort);
process.on("SIGTERM", handleAbort);

function render() {
  clearScreen();
  console.log(`=== KILO ORCHESTRATOR DASHBOARD ===  [${new Date().toLocaleTimeString()}]`);
  console.log(`🛑 Press Ctrl+C or close this window to safely abort all agents.\n`);

  try {
    const agents = JSON.parse(fs.readFileSync(agentsFile, "utf-8"));
    const agentNames = Object.keys(agents);
    console.log("🟢 AGENT STATUS");
    if (agentNames.length === 0) {
      console.log("No agents running yet.");
    } else {
      console.table(
        agentNames.map((name) => {
          let extraInfo = agents[name].task.slice(0, 40) + (agents[name].task.length > 40 ? "..." : "");
          
          if (agents[name].status === "errored") {
            try {
              const logPath = `kilo-${name}.log`;
              if (fs.existsSync(logPath)) {
                const logs = fs.readFileSync(logPath, "utf-8").trim().split("\n");
                const lastLine = logs[logs.length - 1];
                if (lastLine) extraInfo = `ERROR: ${lastLine.slice(0, 40)}`;
              }
            } catch (e) {}
          }

          return {
            Agent: name,
            Status: agents[name].status,
            CLI: agents[name].cli || "kilo",
            PID: agents[name].pid,
            Info: extraInfo,
          };
        })
      );
    }
  } catch (e) {
    console.log("Waiting for agents.json...");
  }

  console.log("\n🟡 PENDING REQUESTS");
  try {
    const requests = JSON.parse(fs.readFileSync(requestsFile, "utf-8"));
    const pending = requests.filter((r: any) => r.status === "pending");
    if (pending.length === 0) {
      console.log("No pending requests.");
    } else {
      console.table(
        pending.map((r: any) => ({
          ID: r.request_id,
          Agent: r.agent,
          Type: r.type,
          Priority: r.priority,
        }))
      );
    }
  } catch (e) {
    console.log("Waiting for requests.json...");
  }
}

setInterval(render, 2000);
render();
