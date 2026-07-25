import { EventEmitter } from "node:events";
import WebSocket from "ws";

type JsonObject = Record<string, unknown>;

interface CdpPendingCommand {
  resolve(value: unknown): void;
  reject(error: unknown): void;
  method: string;
}

interface CdpErrorShape {
  message?: string;
}

interface CdpCommandResult<T> {
  result?: T;
  error?: CdpErrorShape;
}

interface CreatePageSessionOptions {
  initialUrl?: string;
  visible?: boolean;
}

export class TargetSession extends EventEmitter {
  constructor(
    private readonly client: CdpClient,
    public readonly targetId: string,
    public readonly sessionId: string,
  ) {
    super();
  }

  async send<T>(method: string, params: JsonObject = {}): Promise<T> {
    return this.client.sendSessionCommand<T>(this.sessionId, method, params);
  }

  handleEvent(method: string, params: JsonObject): void {
    this.emit(method, params);
    this.emit("event", { method, params });
  }

  async waitForEvent<T extends JsonObject>(
    method: string,
    predicate?: (params: T) => boolean,
    timeoutMs = 30_000,
  ): Promise<T> {
    return new Promise<T>((resolve, reject) => {
      const timeout = setTimeout(() => {
        this.off(method, listener);
        reject(new Error(`Timed out waiting for ${method}`));
      }, timeoutMs);

      const listener = (params: T): void => {
        if (predicate && !predicate(params)) {
          return;
        }
        clearTimeout(timeout);
        this.off(method, listener);
        resolve(params);
      };

      this.on(method, listener);
    });
  }
}

export class CdpClient {
  private readonly ws: WebSocket;
  private readonly pending = new Map<number, CdpPendingCommand>();
  private readonly sessions = new Map<string, TargetSession>();
  private nextId = 1;

  private constructor(ws: WebSocket) {
    this.ws = ws;
    this.ws.on("message", (raw) => {
      this.handleMessage(raw.toString());
    });
  }

  static async connect(browserWsUrl: string): Promise<CdpClient> {
    const ws = await new Promise<WebSocket>((resolve, reject) => {
      const socket = new WebSocket(browserWsUrl);
      socket.once("open", () => resolve(socket));
      socket.once("error", (error) => reject(error));
    });

    return new CdpClient(ws);
  }

  private handleMessage(rawMessage: string): void {
    const message = JSON.parse(rawMessage) as {
      id?: number;
      sessionId?: string;
      method?: string;
      params?: JsonObject;
      result?: unknown;
      error?: CdpErrorShape;
    };

    if (typeof message.id === "number") {
      const pending = this.pending.get(message.id);
      if (!pending) {
        return;
      }
      this.pending.delete(message.id);
      if (message.error) {
        pending.reject(new Error(`${pending.method}: ${message.error.message ?? "Unknown CDP error"}`));
        return;
      }
      pending.resolve(message.result);
      return;
    }

    if (typeof message.sessionId === "string" && typeof message.method === "string") {
      const session = this.sessions.get(message.sessionId);
      if (session) {
        session.handleEvent(message.method, (message.params ?? {}) as JsonObject);
      }
    }
  }

  private async sendCommand<T>(
    method: string,
    params: JsonObject = {},
    sessionId?: string,
  ): Promise<T> {
    const id = this.nextId;
    this.nextId += 1;

    const payload = sessionId ? { id, method, params, sessionId } : { id, method, params };

    const result = new Promise<T>((resolve, reject) => {
      this.pending.set(id, {
        resolve: (value) => resolve(value as T),
        reject,
        method,
      });
    });

    this.ws.send(JSON.stringify(payload));
    return result;
  }

  async sendBrowserCommand<T>(method: string, params: JsonObject = {}): Promise<T> {
    return this.sendCommand<T>(method, params);
  }

  async sendSessionCommand<T>(sessionId: string, method: string, params: JsonObject = {}): Promise<T> {
    return this.sendCommand<T>(method, params, sessionId);
  }

  private async createPageTarget(initialUrl: string, visible = false): Promise<{ targetId: string }> {
    const attempts: JsonObject[] = visible
      ? [
          {
            url: initialUrl,
            newWindow: true,
            focus: true,
          },
          {
            url: initialUrl,
            focus: true,
          },
          {
            url: initialUrl,
          },
        ]
      : [
          {
            url: initialUrl,
            hidden: true,
          },
          {
            url: initialUrl,
            background: true,
            focus: false,
          },
          {
            url: initialUrl,
          },
        ];

    let lastError: unknown;

    for (const params of attempts) {
      try {
        return await this.sendBrowserCommand<{ targetId: string }>("Target.createTarget", params);
      } catch (error) {
        lastError = error;
      }
    }

    throw lastError instanceof Error ? lastError : new Error("Target.createTarget failed");
  }

  async createPageSession(options: CreatePageSessionOptions = {}): Promise<TargetSession> {
    const initialUrl = options.initialUrl ?? "about:blank";
    const created = await this.createPageTarget(initialUrl, Boolean(options.visible));
    const attached = await this.sendBrowserCommand<{ sessionId: string }>("Target.attachToTarget", {
      targetId: created.targetId,
      flatten: true,
    });

    const session = new TargetSession(this, created.targetId, attached.sessionId);
    this.sessions.set(attached.sessionId, session);

    if (options.visible) {
      await this.sendBrowserCommand("Target.activateTarget", {
        targetId: created.targetId,
      }).catch(() => {});
    }

    await session.send("Page.enable");
    await session.send("Runtime.enable");
    await session.send("DOM.enable");

    if (options.visible) {
      await session.send("Page.bringToFront").catch(() => {});
    }

    return session;
  }

  async closeTarget(targetId: string): Promise<void> {
    try {
      await this.sendBrowserCommand("Target.closeTarget", { targetId });
    } catch {
      // Target may already be gone.
    }
  }

  async close(): Promise<void> {
    await new Promise<void>((resolve) => {
      if (this.ws.readyState === WebSocket.CLOSED) {
        resolve();
        return;
      }
      this.ws.once("close", () => resolve());
      this.ws.close();
    });
  }
}

export async function evaluateRuntime<T>(session: TargetSession, expression: string): Promise<T> {
  const response = await session.send<CdpCommandResult<{ value?: T; description?: string }>>("Runtime.evaluate", {
    expression,
    awaitPromise: true,
    returnByValue: true,
  });

  if (response.error) {
    throw new Error(response.error.message ?? "Runtime.evaluate failed");
  }

  return (response.result?.value as T | undefined) ?? (undefined as T);
}
