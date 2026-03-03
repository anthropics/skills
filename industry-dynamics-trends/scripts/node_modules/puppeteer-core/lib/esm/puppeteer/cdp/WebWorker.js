import { CDPSessionEvent } from '../api/CDPSession.js';
import { TargetType } from '../api/Target.js';
import { WebWorker } from '../api/WebWorker.js';
import { TimeoutSettings } from '../common/TimeoutSettings.js';
import { debugError } from '../common/util.js';
import { ExecutionContext } from './ExecutionContext.js';
import { IsolatedWorld } from './IsolatedWorld.js';
/**
 * @internal
 */
export class CdpWebWorker extends WebWorker {
    #world;
    #client;
    #id;
    #targetType;
    constructor(client, url, targetId, targetType, consoleAPICalled, exceptionThrown, networkManager) {
        super(url);
        this.#id = targetId;
        this.#client = client;
        this.#targetType = targetType;
        this.#world = new IsolatedWorld(this, new TimeoutSettings());
        this.#client.once('Runtime.executionContextCreated', async (event) => {
            this.#world.setContext(new ExecutionContext(client, event.context, this.#world));
        });
        this.#world.emitter.on('consoleapicalled', async (event) => {
            try {
                return consoleAPICalled(this.#world, event);
            }
            catch (err) {
                debugError(err);
            }
        });
        this.#client.on('Runtime.exceptionThrown', exceptionThrown);
        this.#client.once(CDPSessionEvent.Disconnected, () => {
            this.#world.dispose();
        });
        // This might fail if the target is closed before we receive all execution contexts.
        networkManager?.addClient(this.#client).catch(debugError);
        this.#client.send('Runtime.enable').catch(debugError);
    }
    mainRealm() {
        return this.#world;
    }
    get client() {
        return this.#client;
    }
    async close() {
        switch (this.#targetType) {
            case TargetType.SERVICE_WORKER: {
                // For service workers we need to close the target and detach to allow
                // the worker to stop.
                await this.client.connection()?.send('Target.closeTarget', {
                    targetId: this.#id,
                });
                await this.client.connection()?.send('Target.detachFromTarget', {
                    sessionId: this.client.id(),
                });
                break;
            }
            case TargetType.SHARED_WORKER: {
                await this.client.connection()?.send('Target.closeTarget', {
                    targetId: this.#id,
                });
                break;
            }
            default:
                await this.evaluate(() => {
                    self.close();
                });
        }
    }
}
//# sourceMappingURL=WebWorker.js.map