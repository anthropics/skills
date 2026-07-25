import type { Adapter, AdapterInput } from "./types";
import { genericAdapter } from "./generic";
import { hnAdapter } from "./hn";
import { xAdapter } from "./x";
import { youtubeAdapter } from "./youtube";

const adapters: Adapter[] = [xAdapter, youtubeAdapter, hnAdapter, genericAdapter];

export function listAdapters(): Adapter[] {
  return adapters;
}

export function resolveAdapter(input: AdapterInput, forcedName?: string): Adapter {
  if (forcedName) {
    const forced = adapters.find((adapter) => adapter.name === forcedName);
    if (!forced) {
      throw new Error(`Unknown adapter: ${forcedName}`);
    }
    return forced;
  }

  const matched = adapters.find((adapter) => adapter.match(input));
  if (!matched) {
    throw new Error("No adapter matched the URL");
  }
  return matched;
}

export { genericAdapter };
