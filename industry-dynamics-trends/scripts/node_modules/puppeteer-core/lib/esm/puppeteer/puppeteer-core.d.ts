/**
 * @license
 * Copyright 2017 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
export * from './index.js';
import * as Puppeteer from './index.js';
/**
 * @public
 */
declare const puppeteer: Puppeteer.PuppeteerNode;
export declare const 
/**
 * @public
 */
connect: (options: Puppeteer.ConnectOptions) => Promise<Puppeteer.Browser>, 
/**
 * @public
 */
defaultArgs: (options?: Puppeteer.LaunchOptions) => string[], 
/**
 * @public
 */
executablePath: {
    (channel: Puppeteer.ChromeReleaseChannel): string;
    (options: Puppeteer.LaunchOptions): string;
    (): string;
}, 
/**
 * @public
 */
launch: (options?: Puppeteer.LaunchOptions) => Promise<Puppeteer.Browser>;
export default puppeteer;
//# sourceMappingURL=puppeteer-core.d.ts.map