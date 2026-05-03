#!/usr/bin/env ts-node

import * as fs from "fs";
import * as path from "path";

interface BootstrapArgs {
  coordDir: string;
  project: string;
  requirements: string[];
  constraints: string[];
  chatContext: string;
}

function parseArgs(): BootstrapArgs {
  const args = process.argv.slice(2);
  const config: BootstrapArgs = {
    coordDir: "./coord",
    project: "",
    requirements: [],
    constraints: [],
    chatContext: "",
  };

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case "--coord":
        config.coordDir = args[++i];
        break;
      case "--project":
        config.project = args[++i];
        break;
      case "--requirements":
        config.requirements = args[++i].split(",").map((s) => s.trim());
        break;
      case "--constraints":
        config.constraints = args[++i].split(",").map((s) => s.trim());
        break;
      case "--chat-context":
        config.chatContext = args[++i];
        break;
      case "--help":
        console.log(`
Bootstrap Kilo Code Multi-Agent Coordination

Options:
  --coord <dir>              Path to coordination directory (default: ./coord)
  --project <description>    Project description (required)
  --requirements <list>      Comma-separated requirements
  --constraints <list>       Comma-separated constraints
  --chat-context <string>    Compacted summary of original conversation context
  --help                     Show this help message

Example:
  npx ts-node bootstrap.ts --project "Build a chat app" --requirements "Websockets, React" --chat-context "User prefers dark mode"
`);
        process.exit(0);
    }
  }

  if (!config.project) {
    console.error("Error: --project is required.");
    process.exit(1);
  }

  return config;
}

function bootstrap(config: BootstrapArgs): void {
  const { coordDir, project, requirements, constraints, chatContext } = config;

  if (fs.existsSync(coordDir)) {
    console.log(`Directory ${coordDir} already exists. Skipping creation.`);
  } else {
    fs.mkdirSync(coordDir, { recursive: true });
  }

  const context = {
    project,
    chat_context: chatContext,
    requirements,
    constraints,
    created_at: new Date().toISOString(),
  };
  fs.writeFileSync(path.join(coordDir, "context.json"), JSON.stringify(context, null, 2) + "\n");

  fs.writeFileSync(path.join(coordDir, "decisions.json"), "[]\n");
  fs.writeFileSync(path.join(coordDir, "requests.json"), "[]\n");
  fs.writeFileSync(path.join(coordDir, "agents.json"), "{}\n");

  const agentsMd = `# Kilo Code Multi-Agent Coordination

This project is being developed by multiple Kilo Code agents working in parallel.
All agents MUST read and follow these rules.

## Coordination Protocol
- Read \`coord/context.json\` and \`coord/decisions.json\` before starting work.
- Follow all existing decisions strictly. Do not re-decide settled matters.
- If blocked or missing info, DO NOT ASSUME. Write a request to \`coord/requests.json\` and ask for review (see format below).
- Do NOT modify files outside your assigned scope.
- **When you finish your task, you MUST submit a \`review_request\` to \`coord/requests.json\`. Do not just stop working without notifying the orchestrator.**

## Request Format
When you need a decision, review, or clarification, append to \`coord/requests.json\`:
\`\`\`json
{
  "request_id": "<unique-id>",
  "agent": "<your-agent-name>",
  "type": "question|change|conflict|review_request",
  "priority": "low|medium|high",
  "content": "Detailed explanation of the issue or request. Include relevant code snippets.",
  "status": "pending",
  "created_at": "<ISO-timestamp>"
}
\`\`\`
If priority is \`high\`, STOP WORKING and wait for the orchestrator to update \`decisions.json\`.
`;

  fs.writeFileSync("AGENTS.md", agentsMd);

  console.log(`Successfully bootstrapped multi-agent coordination in ${coordDir}`);
  console.log(`Global rules written to AGENTS.md`);
}

bootstrap(parseArgs());
