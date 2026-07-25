import { logger } from './logger.js';

export function get_nested_value<T = unknown>(data: unknown, path: number[], def?: T): T {
  let cur: unknown = data;
  for (let i = 0; i < path.length; i++) {
    const k = path[i]!;
    if (!Array.isArray(cur)) {
      logger.debug(`Safe navigation: path ${JSON.stringify(path)} ended at index ${i} (key '${k}'), returning default.`);
      return def as T;
    }
    cur = cur[k];
    if (cur === undefined) {
      logger.debug(`Safe navigation: path ${JSON.stringify(path)} ended at index ${i} (key '${k}'), returning default.`);
      return def as T;
    }
  }

  if (cur == null && def !== undefined) return def as T;
  return cur as T;
}

export function extract_json_from_response(text: string): unknown {
  if (typeof text !== 'string') {
    throw new TypeError(`Input text is expected to be a string, got ${typeof text} instead.`);
  }

  let last: unknown = undefined;
  for (const line of text.split(/\r?\n/)) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    try {
      last = JSON.parse(trimmed) as unknown;
    } catch {}
  }

  if (last === undefined) {
    throw new Error('Could not find a valid JSON object or array in the response.');
  }

  return last;
}

export const extractJsonFromResponse = extract_json_from_response;
export const getNestedValue = get_nested_value;
