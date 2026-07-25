import { APIError, ImageGenerationError } from '../exceptions.js';
import { sleep } from './http.js';

export function running(retry: number = 0) {
  return <TArgs extends unknown[], TResult>(
    fn: (client: any, ...args: TArgs) => Promise<TResult>,
  ): ((client: any, ...args: TArgs) => Promise<TResult>) => {
    const wrap = async (client: any, ...args: TArgs): Promise<TResult> => {
      try {
        if (!client?._running) {
          await client.init?.({
            timeout: client.timeout,
            auto_close: client.auto_close,
            close_delay: client.close_delay,
            auto_refresh: client.auto_refresh,
            refresh_interval: client.refresh_interval,
            verbose: false,
          });
        }
        return await fn(client, ...args);
      } catch (e) {
        let r = retry;
        if (e instanceof ImageGenerationError) r = Math.min(1, r);
        if (e instanceof APIError && r > 0) {
          await sleep(1000);
          return await running(r - 1)(fn)(client, ...args);
        }
        throw e;
      }
    };
    return wrap;
  };
}

