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
exports.resolveDownloadUrl = resolveDownloadUrl;
exports.resolveDownloadPath = resolveDownloadPath;
exports.relativeExecutablePath = relativeExecutablePath;
exports.changeBaseVersionUrlForTesting = changeBaseVersionUrlForTesting;
exports.resetBaseVersionUrlForTesting = resetBaseVersionUrlForTesting;
exports.getLastKnownGoodReleaseForChannel = getLastKnownGoodReleaseForChannel;
exports.getLastKnownGoodReleaseForMilestone = getLastKnownGoodReleaseForMilestone;
exports.getLastKnownGoodReleaseForBuild = getLastKnownGoodReleaseForBuild;
exports.resolveBuildId = resolveBuildId;
exports.resolveSystemExecutablePaths = resolveSystemExecutablePaths;
exports.resolveDefaultUserDataDir = resolveDefaultUserDataDir;
exports.compareVersions = compareVersions;
const node_child_process_1 = require("node:child_process");
const node_os_1 = __importDefault(require("node:os"));
const node_path_1 = __importDefault(require("node:path"));
const semver_1 = __importDefault(require("semver"));
const httpUtil_js_1 = require("../httpUtil.js");
const types_js_1 = require("./types.js");
function folder(platform) {
    switch (platform) {
        case types_js_1.BrowserPlatform.LINUX_ARM:
        case types_js_1.BrowserPlatform.LINUX:
            return 'linux64';
        case types_js_1.BrowserPlatform.MAC_ARM:
            return 'mac-arm64';
        case types_js_1.BrowserPlatform.MAC:
            return 'mac-x64';
        case types_js_1.BrowserPlatform.WIN32:
            return 'win32';
        case types_js_1.BrowserPlatform.WIN64:
            return 'win64';
    }
}
function resolveDownloadUrl(platform, buildId, baseUrl = 'https://storage.googleapis.com/chrome-for-testing-public') {
    return `${baseUrl}/${resolveDownloadPath(platform, buildId).join('/')}`;
}
function resolveDownloadPath(platform, buildId) {
    return [buildId, folder(platform), `chrome-${folder(platform)}.zip`];
}
function relativeExecutablePath(platform, _buildId) {
    switch (platform) {
        case types_js_1.BrowserPlatform.MAC:
        case types_js_1.BrowserPlatform.MAC_ARM:
            return node_path_1.default.join('chrome-' + folder(platform), 'Google Chrome for Testing.app', 'Contents', 'MacOS', 'Google Chrome for Testing');
        case types_js_1.BrowserPlatform.LINUX_ARM:
        case types_js_1.BrowserPlatform.LINUX:
            return node_path_1.default.join('chrome-linux64', 'chrome');
        case types_js_1.BrowserPlatform.WIN32:
        case types_js_1.BrowserPlatform.WIN64:
            return node_path_1.default.join('chrome-' + folder(platform), 'chrome.exe');
    }
}
let baseVersionUrl = 'https://googlechromelabs.github.io/chrome-for-testing';
function changeBaseVersionUrlForTesting(url) {
    baseVersionUrl = url;
}
function resetBaseVersionUrlForTesting() {
    baseVersionUrl = 'https://googlechromelabs.github.io/chrome-for-testing';
}
async function getLastKnownGoodReleaseForChannel(channel) {
    const data = (await (0, httpUtil_js_1.getJSON)(new URL(`${baseVersionUrl}/last-known-good-versions.json`)));
    for (const channel of Object.keys(data.channels)) {
        data.channels[channel.toLowerCase()] = data.channels[channel];
        delete data.channels[channel];
    }
    return data.channels[channel];
}
async function getLastKnownGoodReleaseForMilestone(milestone) {
    const data = (await (0, httpUtil_js_1.getJSON)(new URL(`${baseVersionUrl}/latest-versions-per-milestone.json`)));
    return data.milestones[milestone];
}
async function getLastKnownGoodReleaseForBuild(
/**
 * @example `112.0.23`,
 */
buildPrefix) {
    const data = (await (0, httpUtil_js_1.getJSON)(new URL(`${baseVersionUrl}/latest-patch-versions-per-build.json`)));
    return data.builds[buildPrefix];
}
async function resolveBuildId(channel) {
    if (Object.values(types_js_1.ChromeReleaseChannel).includes(channel)) {
        return (await getLastKnownGoodReleaseForChannel(channel)).version;
    }
    if (channel.match(/^\d+$/)) {
        // Potentially a milestone.
        return (await getLastKnownGoodReleaseForMilestone(channel))?.version;
    }
    if (channel.match(/^\d+\.\d+\.\d+$/)) {
        // Potentially a build prefix without the patch version.
        return (await getLastKnownGoodReleaseForBuild(channel))?.version;
    }
    return;
}
const WINDOWS_ENV_PARAM_NAMES = [
    'PROGRAMFILES',
    'ProgramW6432',
    'ProgramFiles(x86)',
    // https://source.chromium.org/chromium/chromium/src/+/main:chrome/installer/mini_installer/README.md
    'LOCALAPPDATA',
];
function getChromeWindowsLocation(channel, locationsPrefixes) {
    if (locationsPrefixes.size === 0) {
        throw new Error('Non of the common Windows Env variables were set');
    }
    let suffix;
    switch (channel) {
        case types_js_1.ChromeReleaseChannel.STABLE:
            suffix = 'Google\\Chrome\\Application\\chrome.exe';
            break;
        case types_js_1.ChromeReleaseChannel.BETA:
            suffix = 'Google\\Chrome Beta\\Application\\chrome.exe';
            break;
        case types_js_1.ChromeReleaseChannel.CANARY:
            suffix = 'Google\\Chrome SxS\\Application\\chrome.exe';
            break;
        case types_js_1.ChromeReleaseChannel.DEV:
            suffix = 'Google\\Chrome Dev\\Application\\chrome.exe';
            break;
    }
    return [...locationsPrefixes.values()].map(l => {
        return node_path_1.default.win32.join(l, suffix);
    });
}
function getWslVariable(variable) {
    try {
        // The Windows env for the paths are not passed down
        // to WSL, so we evoke `cmd.exe` which is usually on the PATH
        // from which the env can be access with all uppercase names.
        // The return value is a Windows Path - `C:\Program Files`.
        const result = (0, node_child_process_1.execSync)(`cmd.exe /c echo %${variable.toLocaleUpperCase()}%`, {
            // We need to ignore the stderr as cmd.exe
            // prints a message about wrong UNC path not supported.
            stdio: ['ignore', 'pipe', 'ignore'],
            encoding: 'utf-8',
        }).trim();
        if (result) {
            return result;
        }
    }
    catch { }
    return;
}
function getWslLocation(channel) {
    const wslVersion = (0, node_child_process_1.execSync)('wslinfo --version', {
        stdio: ['ignore', 'pipe', 'ignore'],
        encoding: 'utf-8',
    }).trim();
    if (!wslVersion) {
        throw new Error('Not in WSL or unsupported version of WSL.');
    }
    const wslPrefixes = new Set();
    for (const name of WINDOWS_ENV_PARAM_NAMES) {
        const wslPrefix = getWslVariable(name);
        if (wslPrefix) {
            wslPrefixes.add(wslPrefix);
        }
    }
    const windowsPath = getChromeWindowsLocation(channel, wslPrefixes);
    return windowsPath.map(path => {
        // The above command returned the Windows paths `C:\Program Files\...\chrome.exe`
        // Use the `wslpath` utility tool to transform into the mounted disk
        return (0, node_child_process_1.execSync)(`wslpath "${path}"`).toString().trim();
    });
}
function getChromeLinuxOrWslLocation(channel) {
    const locations = [];
    switch (channel) {
        case types_js_1.ChromeReleaseChannel.STABLE:
            locations.push('/opt/google/chrome/chrome');
            break;
        case types_js_1.ChromeReleaseChannel.BETA:
            locations.push('/opt/google/chrome-beta/chrome');
            break;
        case types_js_1.ChromeReleaseChannel.CANARY:
            locations.push('/opt/google/chrome-canary/chrome');
            break;
        case types_js_1.ChromeReleaseChannel.DEV:
            locations.push('/opt/google/chrome-unstable/chrome');
            break;
    }
    try {
        const wslPath = getWslLocation(channel);
        if (wslPath) {
            locations.push(...wslPath);
        }
    }
    catch {
        // Ignore WSL errors
    }
    return locations;
}
function resolveSystemExecutablePaths(platform, channel) {
    switch (platform) {
        case types_js_1.BrowserPlatform.WIN64:
        case types_js_1.BrowserPlatform.WIN32:
            const prefixLocation = new Set(WINDOWS_ENV_PARAM_NAMES.map(name => {
                return process.env[name];
            }).filter((l) => {
                return !!l;
            }));
            // Fallbacks in case env vars are misconfigured.
            prefixLocation.add('C:\\Program Files');
            prefixLocation.add('C:\\Program Files (x86)');
            prefixLocation.add('D:\\Program Files');
            prefixLocation.add('D:\\Program Files (x86)');
            return getChromeWindowsLocation(channel, prefixLocation);
        case types_js_1.BrowserPlatform.MAC_ARM:
        case types_js_1.BrowserPlatform.MAC:
            switch (channel) {
                case types_js_1.ChromeReleaseChannel.STABLE:
                    return [
                        '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
                    ];
                case types_js_1.ChromeReleaseChannel.BETA:
                    return [
                        '/Applications/Google Chrome Beta.app/Contents/MacOS/Google Chrome Beta',
                    ];
                case types_js_1.ChromeReleaseChannel.CANARY:
                    return [
                        '/Applications/Google Chrome Canary.app/Contents/MacOS/Google Chrome Canary',
                    ];
                case types_js_1.ChromeReleaseChannel.DEV:
                    return [
                        '/Applications/Google Chrome Dev.app/Contents/MacOS/Google Chrome Dev',
                    ];
            }
        case types_js_1.BrowserPlatform.LINUX_ARM:
        case types_js_1.BrowserPlatform.LINUX:
            return getChromeLinuxOrWslLocation(channel);
    }
}
function resolveDefaultUserDataDir(platform, channel) {
    switch (platform) {
        case types_js_1.BrowserPlatform.WIN64:
        case types_js_1.BrowserPlatform.WIN32:
            // https://source.chromium.org/chromium/chromium/src/+/main:chrome/common/chrome_paths_win.cc;l=42;drc=4c86c7940a47c36b8bf52c134483ef2da86caa62
            switch (channel) {
                case types_js_1.ChromeReleaseChannel.STABLE:
                    return node_path_1.default.join(getLocalAppDataWin(), 'Google', 'Chrome', 'User Data');
                case types_js_1.ChromeReleaseChannel.BETA:
                    return node_path_1.default.join(getLocalAppDataWin(), 'Google', 'Chrome Beta', 'User Data');
                case types_js_1.ChromeReleaseChannel.CANARY:
                    return node_path_1.default.join(getLocalAppDataWin(), 'Google', 'Chrome SxS', 'User Data');
                case types_js_1.ChromeReleaseChannel.DEV:
                    return node_path_1.default.join(getLocalAppDataWin(), 'Google', 'Chrome Dev', 'User Data');
            }
        case types_js_1.BrowserPlatform.MAC_ARM:
        case types_js_1.BrowserPlatform.MAC:
            // https://source.chromium.org/chromium/chromium/src/+/main:chrome/common/chrome_paths_mac.mm;l=86;drc=4c86c7940a47c36b8bf52c134483ef2da86caa62
            switch (channel) {
                case types_js_1.ChromeReleaseChannel.STABLE:
                    return node_path_1.default.join(getBaseUserDataDirPathMac(), 'Chrome');
                case types_js_1.ChromeReleaseChannel.BETA:
                    return node_path_1.default.join(getBaseUserDataDirPathMac(), 'Chrome Beta');
                case types_js_1.ChromeReleaseChannel.DEV:
                    return node_path_1.default.join(getBaseUserDataDirPathMac(), 'Chrome Dev');
                case types_js_1.ChromeReleaseChannel.CANARY:
                    return node_path_1.default.join(getBaseUserDataDirPathMac(), 'Chrome Canary');
            }
        case types_js_1.BrowserPlatform.LINUX_ARM:
        case types_js_1.BrowserPlatform.LINUX:
            // https://source.chromium.org/chromium/chromium/src/+/main:chrome/common/chrome_paths_linux.cc;l=80;drc=4c86c7940a47c36b8bf52c134483ef2da86caa62
            switch (channel) {
                case types_js_1.ChromeReleaseChannel.STABLE:
                    return node_path_1.default.join(getConfigHomeLinux(), 'google-chrome');
                case types_js_1.ChromeReleaseChannel.BETA:
                    return node_path_1.default.join(getConfigHomeLinux(), 'google-chrome-beta');
                case types_js_1.ChromeReleaseChannel.CANARY:
                    return node_path_1.default.join(getConfigHomeLinux(), 'google-chrome-canary');
                case types_js_1.ChromeReleaseChannel.DEV:
                    return node_path_1.default.join(getConfigHomeLinux(), 'google-chrome-unstable');
            }
    }
}
function getLocalAppDataWin() {
    return (process.env['LOCALAPPDATA'] || node_path_1.default.join(node_os_1.default.homedir(), 'AppData', 'Local'));
}
function getConfigHomeLinux() {
    return (process.env['CHROME_CONFIG_HOME'] ||
        process.env['XDG_CONFIG_HOME'] ||
        node_path_1.default.join(node_os_1.default.homedir(), '.config'));
}
function getBaseUserDataDirPathMac() {
    return node_path_1.default.join(node_os_1.default.homedir(), 'Library', 'Application Support', 'Google');
}
function compareVersions(a, b) {
    if (!semver_1.default.valid(a)) {
        throw new Error(`Version ${a} is not a valid semver version`);
    }
    if (!semver_1.default.valid(b)) {
        throw new Error(`Version ${b} is not a valid semver version`);
    }
    if (semver_1.default.gt(a, b)) {
        return 1;
    }
    else if (semver_1.default.lt(a, b)) {
        return -1;
    }
    else {
        return 0;
    }
}
//# sourceMappingURL=chrome.js.map