import { GRPC } from '../constants.js';
import { APIError } from '../exceptions.js';
import { Gem, GemJar, RPCData } from '../types/index.js';
import { logger } from '../utils/logger.js';
import { extract_json_from_response, get_nested_value } from '../utils/parsing.js';

export abstract class GemMixin {
  protected _gems: GemJar | null = null;

  protected abstract _run<T>(fn: () => Promise<T>, retry: number): Promise<T>;
  protected abstract _batch_execute(payloads: RPCData[], opts?: RequestInit): Promise<Response>;
  protected abstract close(delay?: number): Promise<void>;

  get gems(): GemJar {
    if (this._gems == null) {
      throw new Error(
        'Gems not fetched yet. Call `GeminiClient.fetch_gems()` method to fetch gems from gemini.google.com.',
      );
    }
    return this._gems;
  }

  async fetch_gems(include_hidden: boolean = false, opts?: RequestInit): Promise<GemJar> {
    return await this._run(async () => {
      const res = await this._batch_execute(
        [
          new RPCData(GRPC.LIST_GEMS, include_hidden ? '[4]' : '[3]', 'system'),
          new RPCData(GRPC.LIST_GEMS, '[2]', 'custom'),
        ],
        opts,
      );

      let response_json: unknown;
      try {
        response_json = extract_json_from_response(await res.text());
        if (!Array.isArray(response_json)) throw new Error('Invalid response');
      } catch {
        await this.close();
        throw new APIError('Failed to fetch gems. Invalid response data received. Client will try to re-initialize on next request.');
      }

      let predefined: unknown[] = [];
      let custom: unknown[] = [];

      try {
        for (const part of response_json as unknown[]) {
          if (!Array.isArray(part)) continue;
          const ident = part[part.length - 1];
          const body = get_nested_value<string | null>(part, [2], null);
          if (!body) continue;

          if (ident === 'system') {
            const parsed = JSON.parse(body) as unknown[];
            predefined = (Array.isArray(parsed) ? (parsed[2] as unknown[]) : []) ?? [];
          } else if (ident === 'custom') {
            const parsed = JSON.parse(body) as unknown[] | null;
            if (parsed) custom = (parsed[2] as unknown[]) ?? [];
          }
        }

        if (predefined.length === 0 && custom.length === 0) throw new Error('No gems');
      } catch {
        await this.close();
        logger.debug('Invalid response while parsing gems');
        throw new APIError('Failed to fetch gems. Invalid response data received. Client will try to re-initialize on next request.');
      }

      const entries: [string, Gem][] = [];

      for (const gem of predefined) {
        if (!Array.isArray(gem)) continue;
        const id = String(get_nested_value(gem, [0], ''));
        if (!id) continue;
        entries.push([
          id,
          new Gem(
            id,
            String(get_nested_value(gem, [1, 0], '')),
            get_nested_value<string | null>(gem, [1, 1], null),
            get_nested_value<string | null>(gem, [2, 0], null),
            true,
          ),
        ]);
      }

      for (const gem of custom) {
        if (!Array.isArray(gem)) continue;
        const id = String(get_nested_value(gem, [0], ''));
        if (!id) continue;
        entries.push([
          id,
          new Gem(
            id,
            String(get_nested_value(gem, [1, 0], '')),
            get_nested_value<string | null>(gem, [1, 1], null),
            get_nested_value<string | null>(gem, [2, 0], null),
            false,
          ),
        ]);
      }

      this._gems = new GemJar(entries);
      return this._gems;
    }, 2);
  }

  async create_gem(name: string, prompt: string, description: string = ''): Promise<Gem> {
    return await this._run(async () => {
      const payload = JSON.stringify([
        [
          name,
          description,
          prompt,
          null,
          null,
          null,
          null,
          null,
          0,
          null,
          1,
          null,
          null,
          null,
          [],
        ],
      ]);

      const res = await this._batch_execute([new RPCData(GRPC.CREATE_GEM, payload)]);
      try {
        const response_json = extract_json_from_response(await res.text()) as unknown[];
        const gem_id = JSON.parse(String((response_json[0] as unknown[])[2]))[0] as string;
        return new Gem(gem_id, name, description, prompt, false);
      } catch {
        await this.close();
        throw new APIError('Failed to create gem. Invalid response data received. Client will try to re-initialize on next request.');
      }
    }, 2);
  }

  async update_gem(gem: Gem | string, name: string, prompt: string, description: string = ''): Promise<Gem> {
    return await this._run(async () => {
      const gem_id = typeof gem === 'string' ? gem : gem.id;
      const payload = JSON.stringify([
        gem_id,
        [
          name,
          description,
          prompt,
          null,
          null,
          null,
          null,
          null,
          0,
          null,
          1,
          null,
          null,
          null,
          [],
          0,
        ],
      ]);

      await this._batch_execute([new RPCData(GRPC.UPDATE_GEM, payload)]);
      return new Gem(gem_id, name, description, prompt, false);
    }, 2);
  }

  async delete_gem(gem: Gem | string, opts?: RequestInit): Promise<void> {
    return await this._run(async () => {
      const gem_id = typeof gem === 'string' ? gem : gem.id;
      const payload = JSON.stringify([gem_id]);
      await this._batch_execute([new RPCData(GRPC.DELETE_GEM, payload)], opts);
    }, 2);
  }
}

