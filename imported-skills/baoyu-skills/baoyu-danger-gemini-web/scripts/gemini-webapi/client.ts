import { Endpoint, ErrorCode, Headers, Model } from './constants.js';
import { GemMixin } from './components/gem-mixin.js';
import {
  APIError,
  AuthError,
  GeminiError,
  ImageGenerationError,
  ModelInvalid,
  TemporarilyBlocked,
  TimeoutError,
  UsageLimitExceeded,
} from './exceptions.js';
import { Candidate, Gem, GeneratedImage, ModelOutput, RPCData, WebImage } from './types/index.js';
import {
  extract_json_from_response,
  get_access_token,
  get_nested_value,
  logger,
  parse_file_name,
  rotate_1psidts,
  rotate_tasks,
  fetch_with_timeout,
  sleep,
  upload_file,
  write_cookie_file,
  resolveGeminiWebCookiePath,
} from './utils/index.js';

type InitOptions = {
  timeout?: number;
  auto_close?: boolean;
  close_delay?: number;
  auto_refresh?: boolean;
  refresh_interval?: number;
  verbose?: boolean;
};

type RequestKwargs = RequestInit & { timeout_ms?: number };

const GENERATED_IMAGE_URL_PREFIX = 'https://lh3.googleusercontent.com/gg-dl/';

function normalize_headers(h?: HeadersInit): Record<string, string> {
  if (!h) return {};
  if (Array.isArray(h)) return Object.fromEntries(h.map(([k, v]) => [k, v]));
  if (h instanceof Headers) {
    const out: Record<string, string> = {};
    h.forEach((v, k) => {
      out[k] = v;
    });
    return out;
  }
  return { ...(h as Record<string, string>) };
}

function collect_strings(root: unknown, accept: (s: string) => boolean, limit: number = 20): string[] {
  const out: string[] = [];
  const seen = new Set<string>();
  const stack: unknown[] = [root];

  while (stack.length > 0 && out.length < limit) {
    const v = stack.pop();
    if (typeof v === 'string') {
      if (accept(v) && !seen.has(v)) {
        seen.add(v);
        out.push(v);
      }
      continue;
    }

    if (Array.isArray(v)) {
      for (let i = 0; i < v.length; i++) stack.push(v[i]);
      continue;
    }

    if (v && typeof v === 'object') {
      for (const val of Object.values(v as Record<string, unknown>)) stack.push(val);
    }
  }

  return out;
}

function collect_generated_image_urls(root: unknown, limit: number = 4): string[] {
  return collect_strings(root, (s) => s.startsWith(GENERATED_IMAGE_URL_PREFIX), limit);
}

function parse_response_part_body(part: unknown): unknown[] | null {
  if (!Array.isArray(part)) return null;
  const part_body = get_nested_value<string | null>(part, [2], null);
  if (!part_body) return null;
  try {
    const part_json = JSON.parse(part_body) as unknown;
    return Array.isArray(part_json) ? part_json : null;
  } catch {
    return null;
  }
}

function find_generated_image_part(
  response_json: unknown[],
  body_index: number,
  candidate_index: number,
  limit: number = 4,
): { body: unknown[]; urls: string[] } | null {
  for (let part_index = body_index; part_index < response_json.length; part_index++) {
    const part_json = parse_response_part_body(response_json[part_index]);
    if (!part_json) continue;
    const cand = get_nested_value<unknown>(part_json, [4, candidate_index], null);
    if (!cand) continue;
    const urls = collect_generated_image_urls(cand, limit);
    if (urls.length > 0) return { body: part_json, urls };
  }
  return null;
}

export function collect_generated_image_urls_from_response_parts(
  response_json: unknown[],
  body_index: number,
  candidate_index: number,
  limit: number = 4,
): string[] {
  return find_generated_image_part(response_json, body_index, candidate_index, limit)?.urls ?? [];
}

function push_generated_images(
  generated_images: GeneratedImage[],
  urls: string[],
  proxy: string | null,
  cookies: Record<string, string>,
): void {
  for (const url of urls) {
    generated_images.push(new GeneratedImage(url, '[Generated Image]', '', proxy, cookies));
  }
}

export class GeminiClient extends GemMixin {
  public cookies: Record<string, string> = {};
  public proxy: string | null = null;
  public _running: boolean = false;
  public access_token: string | null = null;
  public timeout: number = 300;
  public auto_close: boolean = false;
  public close_delay: number = 300;
  public auto_refresh: boolean = true;
  public refresh_interval: number = 540;
  public kwargs: RequestInit;

  private close_timer: ReturnType<typeof setTimeout> | null = null;
  private refresh_abort: AbortController | null = null;

  constructor(
    secure_1psid: string | null = null,
    secure_1psidts: string | null = null,
    proxy: string | null = null,
    kwargs: RequestInit = {},
  ) {
    super();
    this.proxy = proxy;
    this.kwargs = kwargs;

    if (secure_1psid) {
      this.cookies['__Secure-1PSID'] = secure_1psid;
      if (secure_1psidts) this.cookies['__Secure-1PSIDTS'] = secure_1psidts;
    }
  }

  async init(
    timeoutOrOpts: number | InitOptions = 300,
    auto_close: boolean = false,
    close_delay: number = 300,
    auto_refresh: boolean = true,
    refresh_interval: number = 540,
    verbose: boolean = true,
  ): Promise<void> {
    const opts: InitOptions =
      typeof timeoutOrOpts === 'object'
        ? timeoutOrOpts
        : { timeout: timeoutOrOpts, auto_close, close_delay, auto_refresh, refresh_interval, verbose };

    const timeout = opts.timeout ?? 300;
    const ac = opts.auto_close ?? false;
    const cd = opts.close_delay ?? 300;
    const ar = opts.auto_refresh ?? true;
    const ri = opts.refresh_interval ?? 540;
    const vb = opts.verbose ?? true;

    try {
      const [token, valid] = await get_access_token(this.cookies, this.proxy, vb);
      this.access_token = token;
      this.cookies = valid;
      this._running = true;

      this.timeout = timeout;
      this.auto_close = ac;
      this.close_delay = cd;
      if (this.auto_close) await this.reset_close_task();

      this.auto_refresh = ar;
      this.refresh_interval = ri;

      const sid = this.cookies['__Secure-1PSID'];
      if (sid) {
        const existing = rotate_tasks.get(sid);
        if (existing && existing instanceof AbortController) existing.abort();
        rotate_tasks.delete(sid);
      }

      if (this.auto_refresh && sid) {
        const ctl = new AbortController();
        this.refresh_abort?.abort();
        this.refresh_abort = ctl;
        rotate_tasks.set(sid, ctl);
        void this.start_auto_refresh(ctl.signal);
      }

      await write_cookie_file(this.cookies, resolveGeminiWebCookiePath(), 'client').catch(() => {});

      if (vb) logger.success('Gemini client initialized successfully.');
    } catch (e) {
      await this.close();
      throw e;
    }
  }

  async close(delay: number = 0): Promise<void> {
    if (delay > 0) await sleep(delay * 1000);
    this._running = false;

    if (this.close_timer) {
      clearTimeout(this.close_timer);
      this.close_timer = null;
    }

    this.refresh_abort?.abort();
    this.refresh_abort = null;

    const sid = this.cookies['__Secure-1PSID'];
    const t = sid ? rotate_tasks.get(sid) : null;
    if (t && t instanceof AbortController) t.abort();
    if (sid) rotate_tasks.delete(sid);
  }

  async reset_close_task(): Promise<void> {
    if (this.close_timer) {
      clearTimeout(this.close_timer);
      this.close_timer = null;
    }

    this.close_timer = setTimeout(() => {
      void this.close(0);
    }, this.close_delay * 1000);
    this.close_timer.unref?.();
  }

  async start_auto_refresh(signal: AbortSignal): Promise<void> {
    while (!signal.aborted) {
      let newTs: string | null = null;
      try {
        newTs = await rotate_1psidts(this.cookies, this.proxy);
      } catch (e) {
        if (e instanceof AuthError) {
          logger.warning('AuthError: Failed to refresh cookies. Auto refresh task canceled.');
          return;
        }
        logger.warning(`Unexpected error while refreshing cookies: ${e instanceof Error ? e.message : String(e)}`);
      }

      if (newTs) {
        this.cookies['__Secure-1PSIDTS'] = newTs;
        await write_cookie_file(this.cookies, resolveGeminiWebCookiePath(), 'refresh').catch(() => {});
        logger.debug('Cookies refreshed. New __Secure-1PSIDTS applied.');
      }

      await sleep(this.refresh_interval * 1000, signal);
    }
  }

  protected async _run<T>(fn: () => Promise<T>, retry: number): Promise<T> {
    try {
      if (!this._running) {
        await this.init({
          timeout: this.timeout,
          auto_close: this.auto_close,
          close_delay: this.close_delay,
          auto_refresh: this.auto_refresh,
          refresh_interval: this.refresh_interval,
          verbose: false,
        });

        if (!this._running) {
          throw new APIError('Client initialization failed.');
        }
      }

      return await fn();
    } catch (e) {
      let r = retry;
      if (e instanceof ImageGenerationError) r = Math.min(1, r);
      if (e instanceof APIError && r > 0) {
        await sleep(1000);
        return await this._run(fn, r - 1);
      }
      throw e;
    }
  }

  async generate_content(
    prompt: string,
    files: string[] | null = null,
    model: Model | string | Record<string, unknown> = Model.UNSPECIFIED,
    gem: Gem | string | null = null,
    chat: ChatSession | null = null,
    kwargs: RequestKwargs = {},
  ): Promise<ModelOutput> {
    return await this._run(async () => {
      if (!prompt) throw new Error('Prompt cannot be empty.');

      let mdl: Model;
      if (typeof model === 'string') mdl = Model.from_name(model);
      else if (model instanceof Model) mdl = model;
      else if (model && typeof model === 'object') mdl = Model.from_dict(model);
      else throw new TypeError(`'model' must be a Model instance, string, or dictionary; got ${typeof model}`);

      const gem_id = gem instanceof Gem ? gem.id : gem;

      if (this.auto_close) await this.reset_close_task();

      if (!this.access_token) throw new APIError('Missing access token.');

      const f = files?.length ? files : null;
      const uploaded =
        f &&
        (await Promise.all(
          f.map(async (p) => [[await upload_file(p, this.proxy)], parse_file_name(p)] as [string[], string]),
        ));

      const first = uploaded ? [prompt, 0, null, uploaded] : [prompt];
      const inner: unknown[] = [first, null, chat ? chat.metadata : null];

      if (gem_id) {
        for (let i = 0; i < 16; i++) inner.push(null);
        inner.push(gem_id);
      }

      const f_req = JSON.stringify([null, JSON.stringify(inner)]);
      const body = new URLSearchParams({ at: this.access_token, 'f.req': f_req }).toString();

      const h0 = { ...Headers.GEMINI, ...mdl.model_header, Cookie: Object.entries(this.cookies).map(([k, v]) => `${k}=${v}`).join('; ') };
      const h1 = { ...h0, ...normalize_headers(kwargs.headers) };

      let res: Response;
      try {
        const timeout_ms = typeof kwargs.timeout_ms === 'number' ? kwargs.timeout_ms : this.timeout * 1000;
        const { timeout_ms: _t, ...rest } = kwargs;
        res = await fetch_with_timeout(Endpoint.GENERATE, {
          method: 'POST',
          headers: h1,
          body,
          redirect: 'follow',
          ...this.kwargs,
          ...rest,
          timeout_ms,
        });
      } catch (e) {
        throw new TimeoutError(
          `Generate content request timed out, please try again. If the problem persists, consider setting a higher 'timeout' value when initializing GeminiClient. (${e instanceof Error ? e.message : String(e)})`,
        );
      }

      if (res.status !== 200) {
        await this.close();
        throw new APIError(`Failed to generate contents. Request failed with status code ${res.status}`);
      }

      const txt = await res.text();
      const response_json = extract_json_from_response(txt);

      let body_json: unknown[] | null = null;
      let body_index = 0;

      try {
        if (!Array.isArray(response_json)) throw new Error('Invalid JSON');
        for (let part_index = 0; part_index < response_json.length; part_index++) {
          const part = response_json[part_index];
          if (!Array.isArray(part)) continue;
          const part_body = get_nested_value<string | null>(part, [2], null);
          if (!part_body) continue;
          try {
            const part_json = JSON.parse(part_body) as unknown[];
            if (get_nested_value(part_json, [4], null)) {
              body_index = part_index;
              body_json = part_json;
              break;
            }
          } catch {}
        }
        if (!body_json) throw new Error('No body');
      } catch {
        await this.close();
        try {
          const code = get_nested_value<number>(response_json, [0, 5, 2, 0, 1, 0], -1);
          if (code === ErrorCode.USAGE_LIMIT_EXCEEDED) {
            throw new UsageLimitExceeded(
              `Failed to generate contents. Usage limit of ${mdl.model_name} model has exceeded. Please try switching to another model.`,
            );
          }
          if (code === ErrorCode.MODEL_INCONSISTENT) {
            throw new ModelInvalid(
              'Failed to generate contents. The specified model is inconsistent with the chat history. Please make sure to pass the same `model` parameter when starting a chat session with previous metadata.',
            );
          }
          if (code === ErrorCode.MODEL_HEADER_INVALID) {
            throw new ModelInvalid(
              'Failed to generate contents. The specified model is not available. Please update gemini_webapi to the latest version. If the error persists and is caused by the package, please report it on GitHub.',
            );
          }
          if (code === ErrorCode.IP_TEMPORARILY_BLOCKED) {
            throw new TemporarilyBlocked(
              'Failed to generate contents. Your IP address is temporarily blocked by Google. Please try using a proxy or waiting for a while.',
            );
          }
        } catch (e) {
          if (e instanceof GeminiError) throw e;
        }

        logger.debug(`Invalid response: ${txt.slice(0, 500)}`);
        throw new APIError('Failed to generate contents. Invalid response data received. Client will try to re-initialize on next request.');
      }

      try {
        const candidate_list = get_nested_value<unknown[]>(body_json, [4], []);
        const out: Candidate[] = [];

        for (let candidate_index = 0; candidate_index < candidate_list.length; candidate_index++) {
          const candidate = candidate_list[candidate_index];
          if (!Array.isArray(candidate)) continue;

          const rcid = get_nested_value<string | null>(candidate, [0], null);
          if (!rcid) continue;

          let text = String(get_nested_value(candidate, [1, 0], ''));
          if (/^http:\/\/googleusercontent\.com\/card_content\/\d+/.test(text)) {
            text = String(get_nested_value(candidate, [22, 0], text));
          }

          const thoughts = get_nested_value<string | null>(candidate, [37, 0, 0], null);

          const web_images: WebImage[] = [];
          for (const w of get_nested_value<unknown[]>(candidate, [12, 1], [])) {
            if (!Array.isArray(w)) continue;
            const url = get_nested_value<string | null>(w, [0, 0, 0], null);
            if (!url) continue;
            web_images.push(new WebImage(url, String(get_nested_value(w, [7, 0], '')), String(get_nested_value(w, [0, 4], '')), this.proxy));
          }

          const generated_images: GeneratedImage[] = [];
          const wants_generated =
            get_nested_value(candidate, [12, 7, 0], null) != null ||
            /http:\/\/googleusercontent\.com\/image_generation_content\/\d+/.test(text) ||
            // Gemini 3 no longer emits the legacy marker in the candidate text; the generated
            // image arrives in a later response part. Detect it from the raw response instead.
            /\/gg-dl\//.test(txt) ||
            /image_generation_content\/\d+/.test(txt);

          if (wants_generated) {
            const image_part = find_generated_image_part(response_json as unknown[], body_index, candidate_index, 1);
            const img_body = image_part?.body ?? null;

            // Not every candidate carries a generated image (e.g. multi-candidate responses).
            // If this candidate has no image part, skip extraction instead of failing the whole call.
            const img_candidate = img_body ? get_nested_value<unknown[]>(img_body, [4, candidate_index], []) : [];
            const finished = get_nested_value<string | null>(img_candidate, [1, 0], null);
            if (finished) {
              text = finished.replace(/http:\/\/googleusercontent\.com\/image_generation_content\/\d+/g, '').trimEnd();
            }

            const gen = get_nested_value<unknown[]>(img_candidate, [12, 7, 0], []);
            for (let img_index = 0; img_index < gen.length; img_index++) {
              const g = gen[img_index];
              if (!Array.isArray(g)) continue;
              const url = get_nested_value<string | null>(g, [0, 3, 3], null);
              if (!url) continue;
              const img_num = get_nested_value<number | null>(g, [3, 6], null);
              const title = img_num ? `[Generated Image ${img_num}]` : '[Generated Image]';
              const alt_list = get_nested_value<unknown[]>(g, [3, 5], []);
              const alt =
                (typeof alt_list[img_index] === 'string' ? (alt_list[img_index] as string) : null) ??
                (typeof alt_list[0] === 'string' ? (alt_list[0] as string) : '') ??
                '';
              generated_images.push(new GeneratedImage(url, title, alt, this.proxy, this.cookies));
            }

            if (generated_images.length === 0) {
              push_generated_images(generated_images, collect_generated_image_urls(img_candidate), this.proxy, this.cookies);
            }
          }

          // Fallback: unconditionally scan all response parts for generated image URLs.
          // The `wants_generated` detection above relies on `candidate[12][7][0]` and an old
          // `googleusercontent.com/image_generation_content/` URL pattern, both of which no
          // longer appear in the current Gemini Web API response format.
          // When Gemini does generate images, their URLs now start with
          // `https://lh3.googleusercontent.com/gg-dl/` and are present somewhere in the
          // response parts — this fallback finds them so images are not silently dropped.
          if (generated_images.length === 0) {
            const urls = collect_generated_image_urls_from_response_parts(response_json as unknown[], body_index, candidate_index);
            push_generated_images(generated_images, urls, this.proxy, this.cookies);
          }

          out.push(new Candidate({ rcid, text, thoughts, web_images, generated_images }));
        }

        if (out.length === 0) {
          throw new GeminiError('Failed to generate contents. No output data found in response.');
        }

        const metadata = get_nested_value<string[]>(body_json, [1], []);
        const output = new ModelOutput({ metadata, candidates: out });

        if (chat instanceof ChatSession) chat.last_output = output;
        return output;
      } catch (e) {
        if (e instanceof GeminiError || e instanceof APIError) throw e;
        throw new APIError('Failed to parse response body. Data structure is invalid.');
      }
    }, 2);
  }

  async generateContent(
    prompt: string,
    files?: string[] | null,
    model?: Model | string | Record<string, unknown>,
    gem?: Gem | string | null,
    chat?: ChatSession | null,
    kwargs?: RequestKwargs,
  ): Promise<ModelOutput> {
    return await this.generate_content(prompt, files ?? null, model ?? Model.UNSPECIFIED, gem ?? null, chat ?? null, kwargs ?? {});
  }

  start_chat(opts?: ConstructorParameters<typeof ChatSession>[1]): ChatSession {
    return new ChatSession(this, opts);
  }

  startChat(opts?: ConstructorParameters<typeof ChatSession>[1]): ChatSession {
    return this.start_chat(opts);
  }

  protected async _batch_execute(payloads: RPCData[], opts: RequestInit = {}): Promise<Response> {
    if (!this.access_token) throw new APIError('Missing access token.');

    const f_req = JSON.stringify([payloads.map((p) => p.serialize())]);
    const body = new URLSearchParams({ at: this.access_token, 'f.req': f_req }).toString();

    const h0 = { ...Headers.GEMINI, Cookie: Object.entries(this.cookies).map(([k, v]) => `${k}=${v}`).join('; ') };
    const h1 = { ...h0, ...normalize_headers(opts.headers) };

    const res = await fetch_with_timeout(Endpoint.BATCH_EXEC, {
      method: 'POST',
      headers: h1,
      body,
      redirect: 'follow',
      ...this.kwargs,
      ...opts,
      timeout_ms: this.timeout * 1000,
    });

    if (res.status !== 200) {
      await this.close();
      throw new APIError(`Batch execution failed with status code ${res.status}`);
    }

    return res;
  }
}

export class ChatSession {
  private __metadata: Array<string | null> = [null, null, null];
  public geminiclient: GeminiClient;
  private _last_output: ModelOutput | null = null;
  public model: Model | string | Record<string, unknown>;
  public gem: Gem | string | null;

  constructor(
    geminiclient: GeminiClient,
    opts: {
      metadata?: Array<string | null>;
      cid?: string | null;
      rid?: string | null;
      rcid?: string | null;
      model?: Model | string | Record<string, unknown>;
      gem?: Gem | string | null;
    } = {},
  ) {
    this.geminiclient = geminiclient;
    this.model = opts.model ?? Model.UNSPECIFIED;
    this.gem = opts.gem ?? null;

    if (opts.metadata) this.metadata = opts.metadata;
    if (opts.cid) this.cid = opts.cid;
    if (opts.rid) this.rid = opts.rid;
    if (opts.rcid) this.rcid = opts.rcid;
  }

  toString(): string {
    return `ChatSession(cid='${this.cid}', rid='${this.rid}', rcid='${this.rcid}')`;
  }

  get last_output(): ModelOutput | null {
    return this._last_output;
  }

  set last_output(v: ModelOutput | null) {
    this._last_output = v;
    if (v) {
      this.metadata = (v.metadata ?? []) as Array<string | null>;
      this.rcid = v.rcid;
    }
  }

  async send_message(prompt: string, files: string[] | null = null, kwargs: RequestKwargs = {}): Promise<ModelOutput> {
    return await this.geminiclient.generate_content(prompt, files, this.model, this.gem, this, kwargs);
  }

  async sendMessage(prompt: string, files?: string[] | null, kwargs?: RequestKwargs): Promise<ModelOutput> {
    return await this.send_message(prompt, files ?? null, kwargs ?? {});
  }

  choose_candidate(index: number): ModelOutput {
    if (!this.last_output) throw new Error('No previous output data found in this chat session.');
    if (index >= this.last_output.candidates.length) {
      throw new Error(`Index ${index} exceeds the number of candidates in last model output.`);
    }
    this.last_output.chosen = index;
    this.rcid = this.last_output.rcid;
    return this.last_output;
  }

  chooseCandidate(index: number): ModelOutput {
    return this.choose_candidate(index);
  }

  get metadata(): Array<string | null> {
    return this.__metadata;
  }

  set metadata(v: Array<string | null>) {
    if (v.length > 3) throw new Error('metadata cannot exceed 3 elements');
    this.__metadata = [null, null, null];
    for (let i = 0; i < v.length; i++) this.__metadata[i] = v[i] ?? null;
  }

  get cid(): string | null {
    return this.__metadata[0];
  }

  set cid(v: string | null) {
    this.__metadata[0] = v;
  }

  get rid(): string | null {
    return this.__metadata[1];
  }

  set rid(v: string | null) {
    this.__metadata[1] = v;
  }

  get rcid(): string | null {
    return this.__metadata[2];
  }

  set rcid(v: string | null) {
    this.__metadata[2] = v;
  }
}
