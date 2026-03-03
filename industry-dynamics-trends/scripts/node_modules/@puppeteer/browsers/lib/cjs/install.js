"use strict";
/**
 * @license
 * Copyright 2017 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.install = install;
exports.uninstall = uninstall;
exports.getInstalledBrowsers = getInstalledBrowsers;
exports.canDownload = canDownload;
exports.getDownloadUrl = getDownloadUrl;
exports.makeProgressCallback = makeProgressCallback;
const node_assert_1 = __importDefault(require("node:assert"));
const node_child_process_1 = require("node:child_process");
const node_fs_1 = require("node:fs");
const promises_1 = require("node:fs/promises");
const node_os_1 = __importDefault(require("node:os"));
const node_path_1 = __importDefault(require("node:path"));
const progress_1 = __importDefault(require("progress"));
const browser_data_js_1 = require("./browser-data/browser-data.js");
const Cache_js_1 = require("./Cache.js");
const debug_js_1 = require("./debug.js");
const DefaultProvider_js_1 = require("./DefaultProvider.js");
const detectPlatform_js_1 = require("./detectPlatform.js");
const fileUtil_js_1 = require("./fileUtil.js");
const httpUtil_js_1 = require("./httpUtil.js");
const debugInstall = (0, debug_js_1.debug)('puppeteer:browsers:install');
const times = new Map();
function debugTime(label) {
    times.set(label, process.hrtime());
}
function debugTimeEnd(label) {
    const end = process.hrtime();
    const start = times.get(label);
    if (!start) {
        return;
    }
    const duration = end[0] * 1000 + end[1] / 1e6 - (start[0] * 1000 + start[1] / 1e6); // calculate duration in milliseconds
    debugInstall(`Duration for ${label}: ${duration}ms`);
}
/**
 * Install using custom provider plugins.
 * Tries each provider in order until one succeeds.
 * Falls back to default provider if all custom providers fail.
 *
 * @internal
 */
async function installWithProviders(options) {
    if (!options.platform) {
        throw new Error('Platform must be defined');
    }
    const cache = new Cache_js_1.Cache(options.cacheDir);
    const browserRoot = cache.browserRoot(options.browser);
    // Build provider list with proper fallback behavior
    const providers = [...(options.providers || [])];
    // If custom baseUrl is provided, add it as a provider
    if (options.baseUrl) {
        providers.push(new DefaultProvider_js_1.DefaultProvider(options.baseUrl));
    }
    // Always add default provider as final fallback
    // (unless custom baseUrl is provided and forceFallbackForTesting is false)
    if (!options.baseUrl || options.forceFallbackForTesting) {
        providers.push(new DefaultProvider_js_1.DefaultProvider());
    }
    const downloadOptions = {
        browser: options.browser,
        platform: options.platform,
        buildId: options.buildId,
        progressCallback: options.downloadProgressCallback === 'default'
            ? await makeProgressCallback(options.browser, options.buildIdAlias ?? options.buildId)
            : options.downloadProgressCallback,
    };
    const errors = [];
    for (const provider of providers) {
        try {
            // Check: does this provider support this browser/platform?
            if (!(await provider.supports(downloadOptions))) {
                debugInstall(`Provider ${provider.getName()} does not support ${options.browser} on ${options.platform}`);
                continue;
            }
            // Warn if using non-default provider
            if (!(provider instanceof DefaultProvider_js_1.DefaultProvider)) {
                debugInstall(`⚠️  Using custom downloader: ${provider.getName()}`);
                debugInstall(`⚠️  Puppeteer does not guarantee compatibility with non-default providers`);
            }
            debugInstall(`Trying provider: ${provider.getName()} for ${options.browser} ${options.buildId}`);
            // Get download URL from provider
            const url = await provider.getDownloadUrl(downloadOptions);
            if (!url) {
                debugInstall(`Provider ${provider.getName()} returned no URL for ${options.browser} ${options.buildId}`);
                continue;
            }
            debugInstall(`Successfully got URL from ${provider.getName()}: ${url}`);
            if (!(0, node_fs_1.existsSync)(browserRoot)) {
                await (0, promises_1.mkdir)(browserRoot, { recursive: true });
            }
            // Download and install using the URL from the provider
            return await installUrl(url, options, provider);
        }
        catch (err) {
            debugInstall(`Provider ${provider.getName()} failed: ${err.message}`);
            errors.push({
                providerName: provider.getName(),
                error: err,
            });
            // Continue to next provider
        }
    }
    // All providers failed
    const errorDetails = errors
        .map(e => {
        return `  - ${e.providerName}: ${e.error.message}`;
    })
        .join('\n');
    throw new Error(`All providers failed for ${options.browser} ${options.buildId}:\n${errorDetails}`);
}
async function install(options) {
    options.platform ??= (0, detectPlatform_js_1.detectBrowserPlatform)();
    options.unpack ??= true;
    if (!options.platform) {
        throw new Error(`Cannot download a binary for the provided platform: ${node_os_1.default.platform()} (${node_os_1.default.arch()})`);
    }
    // Always use plugin architecture (uses default provider if none specified)
    options.providers ??= [];
    return await installWithProviders(options);
}
async function installDeps(installedBrowser) {
    if (process.platform !== 'linux' ||
        installedBrowser.platform !== browser_data_js_1.BrowserPlatform.LINUX) {
        return;
    }
    // Currently, only Debian-like deps are supported.
    const depsPath = node_path_1.default.join(node_path_1.default.dirname(installedBrowser.executablePath), 'deb.deps');
    if (!(0, node_fs_1.existsSync)(depsPath)) {
        debugInstall(`deb.deps file was not found at ${depsPath}`);
        return;
    }
    const data = (0, node_fs_1.readFileSync)(depsPath, 'utf-8').split('\n').join(',');
    if (process.getuid?.() !== 0) {
        throw new Error('Installing system dependencies requires root privileges');
    }
    let result = (0, node_child_process_1.spawnSync)('apt-get', ['-v']);
    if (result.status !== 0) {
        throw new Error('Failed to install system dependencies: apt-get does not seem to be available');
    }
    debugInstall(`Trying to install dependencies: ${data}`);
    result = (0, node_child_process_1.spawnSync)('apt-get', [
        'satisfy',
        '-y',
        data,
        '--no-install-recommends',
    ]);
    if (result.status !== 0) {
        throw new Error(`Failed to install system dependencies: status=${result.status},error=${result.error},stdout=${result.stdout.toString('utf8')},stderr=${result.stderr.toString('utf8')}`);
    }
    debugInstall(`Installed system dependencies ${data}`);
}
async function installUrl(url, options, provider) {
    if (!provider) {
        throw new Error('Provider is required for installation');
    }
    options.platform ??= (0, detectPlatform_js_1.detectBrowserPlatform)();
    if (!options.platform) {
        throw new Error(`Cannot download a binary for the provided platform: ${node_os_1.default.platform()} (${node_os_1.default.arch()})`);
    }
    let downloadProgressCallback = options.downloadProgressCallback;
    if (downloadProgressCallback === 'default') {
        downloadProgressCallback = await makeProgressCallback(options.browser, options.buildIdAlias ?? options.buildId);
    }
    const fileName = decodeURIComponent(url.toString()).split('/').pop();
    (0, node_assert_1.default)(fileName, `A malformed download URL was found: ${url}.`);
    const cache = new Cache_js_1.Cache(options.cacheDir);
    const browserRoot = cache.browserRoot(options.browser);
    const archivePath = node_path_1.default.join(browserRoot, `${options.buildId}-${fileName}`);
    if (!(0, node_fs_1.existsSync)(browserRoot)) {
        await (0, promises_1.mkdir)(browserRoot, { recursive: true });
    }
    if (!options.unpack) {
        if ((0, node_fs_1.existsSync)(archivePath)) {
            return archivePath;
        }
        debugInstall(`Downloading binary from ${url}`);
        debugTime('download');
        await (0, httpUtil_js_1.downloadFile)(url, archivePath, downloadProgressCallback);
        debugTimeEnd('download');
        return archivePath;
    }
    const outputPath = cache.installationDir(options.browser, options.platform, options.buildId);
    // Get executable path from provider once (used for both cached and new installations)
    const relativeExecutablePath = await provider.getExecutablePath({
        browser: options.browser,
        buildId: options.buildId,
        platform: options.platform,
    });
    debugInstall(`Using executable path from provider: ${relativeExecutablePath}`);
    const installedBrowser = new Cache_js_1.InstalledBrowser(cache, options.browser, options.buildId, options.platform);
    // Write metadata for the installation (only for non-default providers)
    if (!(provider instanceof DefaultProvider_js_1.DefaultProvider)) {
        cache.writeExecutablePath(options.browser, options.platform, options.buildId, relativeExecutablePath);
    }
    try {
        if ((0, node_fs_1.existsSync)(outputPath)) {
            if (!(0, node_fs_1.existsSync)(installedBrowser.executablePath)) {
                throw new Error(`The browser folder (${outputPath}) exists but the executable (${installedBrowser.executablePath}) is missing`);
            }
            await runSetup(installedBrowser);
            if (options.installDeps) {
                await installDeps(installedBrowser);
            }
            return installedBrowser;
        }
        // Check if archive already exists (e.g., from a custom provider)
        if (!(0, node_fs_1.existsSync)(archivePath)) {
            debugInstall(`Downloading binary from ${url}`);
            try {
                debugTime('download');
                await (0, httpUtil_js_1.downloadFile)(url, archivePath, downloadProgressCallback);
            }
            finally {
                debugTimeEnd('download');
            }
        }
        else {
            debugInstall(`Using existing archive at ${archivePath}`);
        }
        debugInstall(`Installing ${archivePath} to ${outputPath}`);
        try {
            debugTime('extract');
            await (0, fileUtil_js_1.unpackArchive)(archivePath, outputPath);
        }
        finally {
            debugTimeEnd('extract');
        }
        if (options.buildIdAlias) {
            const metadata = installedBrowser.readMetadata();
            metadata.aliases[options.buildIdAlias] = options.buildId;
            installedBrowser.writeMetadata(metadata);
        }
        await runSetup(installedBrowser);
        if (options.installDeps) {
            await installDeps(installedBrowser);
        }
        return installedBrowser;
    }
    finally {
        if ((0, node_fs_1.existsSync)(archivePath)) {
            await (0, promises_1.unlink)(archivePath);
        }
    }
}
async function runSetup(installedBrowser) {
    // On Windows for Chrome invoke setup.exe to configure sandboxes.
    if ((installedBrowser.platform === browser_data_js_1.BrowserPlatform.WIN32 ||
        installedBrowser.platform === browser_data_js_1.BrowserPlatform.WIN64) &&
        installedBrowser.browser === browser_data_js_1.Browser.CHROME &&
        installedBrowser.platform === (0, detectPlatform_js_1.detectBrowserPlatform)()) {
        try {
            debugTime('permissions');
            const browserDir = node_path_1.default.dirname(installedBrowser.executablePath);
            const setupExePath = node_path_1.default.join(browserDir, 'setup.exe');
            if (!(0, node_fs_1.existsSync)(setupExePath)) {
                return;
            }
            (0, node_child_process_1.spawnSync)(node_path_1.default.join(browserDir, 'setup.exe'), [`--configure-browser-in-directory=` + browserDir], {
                shell: true,
            });
            // TODO: Handle error here. Currently the setup.exe sometimes
            // errors although it sets the permissions correctly.
        }
        finally {
            debugTimeEnd('permissions');
        }
    }
}
/**
 *
 * @public
 */
async function uninstall(options) {
    options.platform ??= (0, detectPlatform_js_1.detectBrowserPlatform)();
    if (!options.platform) {
        throw new Error(`Cannot detect the browser platform for: ${node_os_1.default.platform()} (${node_os_1.default.arch()})`);
    }
    new Cache_js_1.Cache(options.cacheDir).uninstall(options.browser, options.platform, options.buildId);
}
/**
 * Returns metadata about browsers installed in the cache directory.
 *
 * @public
 */
async function getInstalledBrowsers(options) {
    return new Cache_js_1.Cache(options.cacheDir).getInstalledBrowsers();
}
/**
 * @public
 */
async function canDownload(options) {
    options.platform ??= (0, detectPlatform_js_1.detectBrowserPlatform)();
    if (!options.platform) {
        throw new Error(`Cannot download a binary for the provided platform: ${node_os_1.default.platform()} (${node_os_1.default.arch()})`);
    }
    // Always use plugin architecture (uses default provider if none specified)
    const providers = [
        ...(options.providers || []),
        new DefaultProvider_js_1.DefaultProvider(options.baseUrl),
    ];
    const downloadOptions = {
        browser: options.browser,
        platform: options.platform,
        buildId: options.buildId,
    };
    // Check if any provider can provide a valid, downloadable URL
    for (const provider of providers) {
        if (!(await provider.supports(downloadOptions))) {
            continue;
        }
        const url = await provider.getDownloadUrl(downloadOptions);
        if (url && (await (0, httpUtil_js_1.headHttpRequest)(url))) {
            return true;
        }
    }
    return false;
}
/**
 * Retrieves a URL for downloading the binary archive of a given browser.
 *
 * The archive is bound to the specific platform and build ID specified.
 *
 * @public
 */
function getDownloadUrl(browser, platform, buildId, baseUrl) {
    return new URL(browser_data_js_1.downloadUrls[browser](platform, buildId, baseUrl));
}
/**
 * @public
 */
function makeProgressCallback(browser, buildId) {
    let progressBar;
    let lastDownloadedBytes = 0;
    return (downloadedBytes, totalBytes) => {
        if (!progressBar) {
            progressBar = new progress_1.default(`Downloading ${browser} ${buildId} - ${toMegabytes(totalBytes)} [:bar] :percent :etas `, {
                complete: '=',
                incomplete: ' ',
                width: 20,
                total: totalBytes,
            });
        }
        const delta = downloadedBytes - lastDownloadedBytes;
        lastDownloadedBytes = downloadedBytes;
        progressBar.tick(delta);
    };
}
function toMegabytes(bytes) {
    const mb = bytes / 1000 / 1000;
    return `${Math.round(mb * 10) / 10} MB`;
}
//# sourceMappingURL=install.js.map