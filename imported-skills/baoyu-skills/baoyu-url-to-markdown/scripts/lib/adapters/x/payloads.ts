import type { AdapterContext } from "../types";
import { filterXGraphQlEntries } from "./shared";

export function getRelevantXThreadEntries(context: AdapterContext) {
  return filterXGraphQlEntries(context.network.getEntries()).filter(
    (entry) =>
      entry.method === "GET" &&
      entry.finished &&
      (
        entry.url.includes("TweetDetail") ||
        entry.url.includes("TweetResultByRestId") ||
        entry.url.includes("TweetResultsByRestIds")
      ),
  );
}

export async function prefetchRelevantXThreadBodies(context: AdapterContext): Promise<void> {
  const entries = getRelevantXThreadEntries(context).filter((entry) => entry.body === undefined && !entry.bodyError);
  for (const entry of entries) {
    await context.network.ensureBody(entry);
  }
}

export async function collectXJsonPayloads(context: AdapterContext): Promise<unknown[]> {
  await prefetchRelevantXThreadBodies(context);
  const entries = getRelevantXThreadEntries(context);

  const payloads: unknown[] = [];
  for (const entry of entries) {
    const payload = await context.network.getJsonBody(entry);
    if (payload) {
      payloads.push(payload);
    }
  }
  return payloads;
}

export async function waitForInitialXPayload(context: AdapterContext): Promise<void> {
  try {
    await context.network.waitForResponse(
      (entry) =>
        entry.url.includes("/graphql/") &&
        (entry.url.includes("TweetDetail") || entry.url.includes("TweetResultByRestId")),
      { timeoutMs: Math.min(context.timeoutMs, 15_000) },
    );
    await prefetchRelevantXThreadBodies(context);
  } catch {
    context.log.debug("No tweet GraphQL response observed before timeout.");
  }
}
