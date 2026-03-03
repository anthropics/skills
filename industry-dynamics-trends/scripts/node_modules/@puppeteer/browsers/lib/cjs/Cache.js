"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.Cache = exports.InstalledBrowser = void 0;
const node_fs_1 = __importDefault(require("node:fs"));
const node_os_1 = __importDefault(require("node:os"));
const node_path_1 = __importDefault(require("node:path"));
const debug_1 = __importDefault(require("debug"));
const browser_data_js_1 = require("./browser-data/browser-data.js");
const detectPlatform_js_1 = require("./detectPlatform.js");
const debugCache = (0, debug_1.default)('puppeteer:browsers:cache');
/**
 * @public
 */
class InstalledBrowser {
    browser;
    buildId;
    platform;
    executablePath;
    #cache;
    /**
     * @internal
     */
    constructor(cache, browser, buildId, platform) {
        this.#cache = cache;
        this.browser = browser;
        this.buildId = buildId;
        this.platform = platform;
        this.executablePath = cache.computeExecutablePath({
            browser,
            buildId,
            platform,
        });
    }
    /**
     * Path to the root of the installation folder. Use
     * {@link computeExecutablePath} to get the path to the executable binary.
     */
    get path() {
        return this.#cache.installationDir(this.browser, this.platform, this.buildId);
    }
    readMetadata() {
        return this.#cache.readMetadata(this.browser);
    }
    writeMetadata(metadata) {
        this.#cache.writeMetadata(this.browser, metadata);
    }
}
exports.InstalledBrowser = InstalledBrowser;
/**
 * The cache used by Puppeteer relies on the following structure:
 *
 * - rootDir
 *   -- <browser1> | browserRoot(browser1)
 *   ---- <platform>-<buildId> | installationDir()
 *   ------ the browser-platform-buildId
 *   ------ specific structure.
 *   -- <browser2> | browserRoot(browser2)
 *   ---- <platform>-<buildId> | installationDir()
 *   ------ the browser-platform-buildId
 *   ------ specific structure.
 *   @internal
 */
class Cache {
    #rootDir;
    constructor(rootDir) {
        this.#rootDir = rootDir;
    }
    /**
     * @internal
     */
    get rootDir() {
        return this.#rootDir;
    }
    browserRoot(browser) {
        return node_path_1.default.join(this.#rootDir, browser);
    }
    metadataFile(browser) {
        return node_path_1.default.join(this.browserRoot(browser), '.metadata');
    }
    readMetadata(browser) {
        const metatadaPath = this.metadataFile(browser);
        if (!node_fs_1.default.existsSync(metatadaPath)) {
            return { aliases: {} };
        }
        // TODO: add type-safe parsing.
        const data = JSON.parse(node_fs_1.default.readFileSync(metatadaPath, 'utf8'));
        if (typeof data !== 'object') {
            throw new Error('.metadata is not an object');
        }
        return data;
    }
    writeMetadata(browser, metadata) {
        const metatadaPath = this.metadataFile(browser);
        node_fs_1.default.mkdirSync(node_path_1.default.dirname(metatadaPath), { recursive: true });
        node_fs_1.default.writeFileSync(metatadaPath, JSON.stringify(metadata, null, 2));
    }
    readExecutablePath(browser, platform, buildId) {
        const metadata = this.readMetadata(browser);
        const key = `${platform}-${buildId}`;
        return metadata.executablePaths?.[key] ?? null;
    }
    writeExecutablePath(browser, platform, buildId, executablePath) {
        const metadata = this.readMetadata(browser);
        if (!metadata.executablePaths) {
            metadata.executablePaths = {};
        }
        const key = `${platform}-${buildId}`;
        metadata.executablePaths[key] = executablePath;
        this.writeMetadata(browser, metadata);
    }
    resolveAlias(browser, alias) {
        const metadata = this.readMetadata(browser);
        if (alias === 'latest') {
            return Object.values(metadata.aliases || {})
                .sort((0, browser_data_js_1.getVersionComparator)(browser))
                .at(-1);
        }
        return metadata.aliases[alias];
    }
    installationDir(browser, platform, buildId) {
        return node_path_1.default.join(this.browserRoot(browser), `${platform}-${buildId}`);
    }
    clear() {
        node_fs_1.default.rmSync(this.#rootDir, {
            force: true,
            recursive: true,
            maxRetries: 10,
            retryDelay: 500,
        });
    }
    uninstall(browser, platform, buildId) {
        const metadata = this.readMetadata(browser);
        for (const alias of Object.keys(metadata.aliases)) {
            if (metadata.aliases[alias] === buildId) {
                delete metadata.aliases[alias];
            }
        }
        // Clean up executable path entry
        const key = `${platform}-${buildId}`;
        if (metadata.executablePaths?.[key]) {
            delete metadata.executablePaths[key];
            this.writeMetadata(browser, metadata);
        }
        node_fs_1.default.rmSync(this.installationDir(browser, platform, buildId), {
            force: true,
            recursive: true,
            maxRetries: 10,
            retryDelay: 500,
        });
    }
    getInstalledBrowsers() {
        if (!node_fs_1.default.existsSync(this.#rootDir)) {
            return [];
        }
        const types = node_fs_1.default.readdirSync(this.#rootDir);
        const browsers = types.filter((t) => {
            return Object.values(browser_data_js_1.Browser).includes(t);
        });
        return browsers.flatMap(browser => {
            const files = node_fs_1.default.readdirSync(this.browserRoot(browser));
            return files
                .map(file => {
                const result = parseFolderPath(node_path_1.default.join(this.browserRoot(browser), file));
                if (!result) {
                    return null;
                }
                return new InstalledBrowser(this, browser, result.buildId, result.platform);
            })
                .filter((item) => {
                return item !== null;
            });
        });
    }
    computeExecutablePath(options) {
        options.platform ??= (0, detectPlatform_js_1.detectBrowserPlatform)();
        if (!options.platform) {
            throw new Error(`Cannot download a binary for the provided platform: ${node_os_1.default.platform()} (${node_os_1.default.arch()})`);
        }
        try {
            options.buildId =
                this.resolveAlias(options.browser, options.buildId) ?? options.buildId;
        }
        catch {
            debugCache('could not read .metadata file for the browser');
        }
        const installationDir = this.installationDir(options.browser, options.platform, options.buildId);
        const storedExecutablePath = this.readExecutablePath(options.browser, options.platform, options.buildId);
        if (storedExecutablePath) {
            // The metadata contains a resolved relative path from the installation dir
            return node_path_1.default.join(installationDir, storedExecutablePath);
        }
        return node_path_1.default.join(installationDir, browser_data_js_1.executablePathByBrowser[options.browser](options.platform, options.buildId));
    }
}
exports.Cache = Cache;
function parseFolderPath(folderPath) {
    const name = node_path_1.default.basename(folderPath);
    const splits = name.split('-');
    if (splits.length !== 2) {
        return;
    }
    const [platform, buildId] = splits;
    if (!buildId || !platform) {
        return;
    }
    return { platform, buildId };
}
//# sourceMappingURL=Cache.js.map