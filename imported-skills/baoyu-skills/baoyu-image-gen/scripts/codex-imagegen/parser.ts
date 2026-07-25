import type { CodexRunResult, ToolCall, TokenUsage } from "./types.ts";

export function parseEventStream(raw: string): Omit<CodexRunResult, "rawLogPath" | "durationMs"> {
  const lines = raw.split("\n").filter((l) => l.trim().length > 0);
  let threadId: string | null = null;
  let agentMessage: string | null = null;
  let usage: TokenUsage | null = null;
  const toolCallsById = new Map<string, ToolCall>();

  for (const line of lines) {
    let event: any;
    try {
      event = JSON.parse(line);
    } catch {
      continue;
    }
    const type = event?.type;
    if (type === "thread.started") {
      threadId = event.thread_id ?? null;
    } else if (type === "item.started" || type === "item.completed") {
      const item = event.item;
      if (!item?.id) continue;
      const tc: ToolCall = {
        id: item.id,
        tool: deriveToolName(item),
        status: item.status ?? (type === "item.completed" ? "completed" : "in_progress"),
        command: item.command,
      };
      toolCallsById.set(item.id, tc);
      if (item.type === "agent_message" && type === "item.completed") {
        agentMessage = String(item.text ?? "");
      }
    } else if (type === "turn.completed") {
      const u = event.usage;
      if (u) {
        usage = {
          input: u.input_tokens ?? 0,
          cached_input: u.cached_input_tokens ?? 0,
          output: u.output_tokens ?? 0,
          reasoning: u.reasoning_output_tokens ?? 0,
        };
      }
    }
  }

  return {
    threadId,
    toolCalls: Array.from(toolCallsById.values()),
    agentMessage,
    usage,
  };
}

function deriveToolName(item: any): string {
  if (item.type === "command_execution") return "shell";
  if (item.type === "agent_message") return "agent_message";
  if (item.type === "image_gen" || item.type === "image_generation") return "image_gen";
  if (typeof item.tool === "string") return item.tool;
  return item.type ?? "unknown";
}

export function hasImageGenInvocation(toolCalls: ToolCall[]): boolean {
  return toolCalls.some((tc) => tc.tool === "image_gen");
}
