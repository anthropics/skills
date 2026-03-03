import { Browser } from 'puppeteer-core';
import { ChromeReleaseChannel } from 'puppeteer-core';
import { ConnectOptions } from 'puppeteer-core';
import { LaunchOptions } from 'puppeteer-core';
import { PuppeteerNode } from 'puppeteer-core';

/**
 * @public
 */
export declare const 
/**
* @public
*/
/**
 * @public
 */
connect: (options: ConnectOptions) => Promise<Browser>;

/**
 * @public
 */
export declare const 
/**
* @public
*/
/**
 * @public
 */
defaultArgs: (options?: LaunchOptions) => string[];

/**
 * @public
 */
export declare const 
/**
* @public
*/
/**
 * @public
 */
executablePath: {
    (channel: ChromeReleaseChannel): string;
    (options: LaunchOptions): string;
    (): string;
};

/**
 * @public
 */
export declare const 
/**
* @public
*/
/**
 * @public
 */
launch: (options?: LaunchOptions) => Promise<Browser>;

/**
 * @public
 */
declare const puppeteer: PuppeteerNode;
export default puppeteer;

/**
 * @public
 */
export declare const 
/**
* @public
*/
/**
 * @public
 */
trimCache: () => Promise<void>;


export * from "puppeteer-core";

export { }
