import type { TargetSession } from "./cdp-client";
import type { Logger } from "../utils/logger";

type JsonObject = Record<string, unknown>;

export interface NetworkEntry {
  requestId: string;
  url: string;
  method: string;
  resourceType: string;
  timestamp: number;
  requestHeaders?: Record<string, string>;
  requestBody?: string;
  status?: number;
  statusText?: string;
  responseHeaders?: Record<string, string>;
  mimeType?: string;
  body?: string;
  bodyBase64?: boolean;
  bodyError?: string;
  failed?: boolean;
  failureReason?: string;
  finished: boolean;
}

function normalizeHeaders(headers: unknown): Record<string, string> | undefined {
  if (!headers || typeof headers !== "object") {
    return undefined;
  }
  return Object.fromEntries(
    Object.entries(headers as Record<string, unknown>).map(([key, value]) => [key, String(value)]),
  );
}

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

export class NetworkJournal {
  private readonly entries = new Map<string, NetworkEntry>();
  private lastActivityAt = Date.now();
  private started = false;

  constructor(
    private readonly session: TargetSession,
    private readonly log: Logger,
  ) {}

  async start(): Promise<void> {
    if (this.started) {
      return;
    }

    this.started = true;
    this.session.on("Network.requestWillBeSent", this.handleRequestWillBeSent);
    this.session.on("Network.responseReceived", this.handleResponseReceived);
    this.session.on("Network.loadingFinished", this.handleLoadingFinished);
    this.session.on("Network.loadingFailed", this.handleLoadingFailed);
    await this.session.send("Network.enable");
  }

  stop(): void {
    if (!this.started) {
      return;
    }
    this.session.off("Network.requestWillBeSent", this.handleRequestWillBeSent);
    this.session.off("Network.responseReceived", this.handleResponseReceived);
    this.session.off("Network.loadingFinished", this.handleLoadingFinished);
    this.session.off("Network.loadingFailed", this.handleLoadingFailed);
    this.started = false;
  }

  private touch(): void {
    this.lastActivityAt = Date.now();
  }

  private readonly handleRequestWillBeSent = (params: JsonObject): void => {
    const requestId = typeof params.requestId === "string" ? params.requestId : undefined;
    const request = params.request as JsonObject | undefined;
    if (!requestId || !request) {
      return;
    }

    this.touch();
    this.entries.set(requestId, {
      requestId,
      url: String(request.url ?? ""),
      method: String(request.method ?? "GET"),
      resourceType: String(params.type ?? "Other"),
      timestamp: Date.now(),
      requestHeaders: normalizeHeaders(request.headers),
      requestBody: typeof request.postData === "string" ? request.postData : undefined,
      finished: false,
    });
  };

  private readonly handleResponseReceived = (params: JsonObject): void => {
    const requestId = typeof params.requestId === "string" ? params.requestId : undefined;
    const response = params.response as JsonObject | undefined;
    if (!requestId || !response) {
      return;
    }

    this.touch();
    const existing = this.entries.get(requestId);
    if (!existing) {
      return;
    }

    existing.status = typeof response.status === "number" ? response.status : undefined;
    existing.statusText = typeof response.statusText === "string" ? response.statusText : undefined;
    existing.responseHeaders = normalizeHeaders(response.headers);
    existing.mimeType = typeof response.mimeType === "string" ? response.mimeType : undefined;
    this.entries.set(requestId, existing);
  };

  private readonly handleLoadingFinished = (params: JsonObject): void => {
    const requestId = typeof params.requestId === "string" ? params.requestId : undefined;
    if (!requestId) {
      return;
    }

    this.touch();
    const existing = this.entries.get(requestId);
    if (!existing) {
      return;
    }
    existing.finished = true;
    this.entries.set(requestId, existing);
  };

  private readonly handleLoadingFailed = (params: JsonObject): void => {
    const requestId = typeof params.requestId === "string" ? params.requestId : undefined;
    if (!requestId) {
      return;
    }

    this.touch();
    const existing = this.entries.get(requestId);
    if (!existing) {
      return;
    }
    existing.finished = true;
    existing.failed = true;
    existing.failureReason = typeof params.errorText === "string" ? params.errorText : "Unknown error";
    this.entries.set(requestId, existing);
  };

  getEntries(): NetworkEntry[] {
    return Array.from(this.entries.values());
  }

  findEntries(predicate: (entry: NetworkEntry) => boolean): NetworkEntry[] {
    return this.getEntries().filter(predicate);
  }

  async waitForIdle(options: { idleMs?: number; timeoutMs?: number } = {}): Promise<void> {
    const idleMs = options.idleMs ?? 1_200;
    const timeoutMs = options.timeoutMs ?? 15_000;
    const startedAt = Date.now();

    while (Date.now() - startedAt < timeoutMs) {
      if (Date.now() - this.lastActivityAt >= idleMs) {
        return;
      }
      await sleep(Math.min(150, idleMs));
    }

    throw new Error("Timed out waiting for network idle");
  }

  async waitForResponse(
    predicate: (entry: NetworkEntry) => boolean,
    options: { timeoutMs?: number } = {},
  ): Promise<NetworkEntry> {
    const timeoutMs = options.timeoutMs ?? 10_000;
    const startedAt = Date.now();

    while (Date.now() - startedAt < timeoutMs) {
      const matched = this.getEntries().find((entry) => entry.finished && predicate(entry));
      if (matched) {
        return matched;
      }
      await sleep(150);
    }

    throw new Error("Timed out waiting for matching network response");
  }

  async ensureBody(entry: NetworkEntry): Promise<string | undefined> {
    if (entry.body !== undefined) {
      return entry.body;
    }
    if (entry.bodyError || entry.failed || !entry.finished) {
      return undefined;
    }

    try {
      const result = await this.session.send<{ body: string; base64Encoded: boolean }>("Network.getResponseBody", {
        requestId: entry.requestId,
      });
      entry.bodyBase64 = result.base64Encoded;
      entry.body = result.base64Encoded ? Buffer.from(result.body, "base64").toString("utf8") : result.body;
      return entry.body;
    } catch (error) {
      entry.bodyError = error instanceof Error ? error.message : String(error);
      this.log.debug(`Failed to fetch response body for ${entry.url}: ${entry.bodyError}`);
      return undefined;
    }
  }

  async getJsonBody(entry: NetworkEntry): Promise<unknown | null> {
    const body = await this.ensureBody(entry);
    if (!body) {
      return null;
    }

    try {
      return JSON.parse(body);
    } catch {
      return null;
    }
  }

  async toJSON(options: { includeBodies?: boolean } = {}): Promise<NetworkEntry[]> {
    const entries = this.getEntries();
    if (!options.includeBodies) {
      return entries;
    }

    await Promise.all(entries.map((entry) => this.ensureBody(entry)));
    return entries;
  }
}

