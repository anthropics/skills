"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.internalConstantsForTesting = void 0;
exports.unpackArchive = unpackArchive;
const node_child_process_1 = require("node:child_process");
const node_fs_1 = require("node:fs");
const promises_1 = require("node:fs/promises");
const path = __importStar(require("node:path"));
const node_stream_1 = require("node:stream");
const debug_1 = __importDefault(require("debug"));
const debugFileUtil = (0, debug_1.default)('puppeteer:browsers:fileUtil');
/**
 * @internal
 */
async function unpackArchive(archivePath, folderPath) {
    if (!path.isAbsolute(folderPath)) {
        folderPath = path.resolve(process.cwd(), folderPath);
    }
    if (archivePath.endsWith('.zip')) {
        const extractZip = await import('extract-zip');
        await extractZip.default(archivePath, { dir: folderPath });
    }
    else if (archivePath.endsWith('.tar.bz2')) {
        await extractTar(archivePath, folderPath, 'bzip2');
    }
    else if (archivePath.endsWith('.dmg')) {
        await (0, promises_1.mkdir)(folderPath);
        await installDMG(archivePath, folderPath);
    }
    else if (archivePath.endsWith('.exe')) {
        // Firefox on Windows.
        const result = (0, node_child_process_1.spawnSync)(archivePath, [`/ExtractDir=${folderPath}`], {
            env: {
                __compat_layer: 'RunAsInvoker',
            },
        });
        if (result.status !== 0) {
            throw new Error(`Failed to extract ${archivePath} to ${folderPath}: ${result.output}`);
        }
    }
    else if (archivePath.endsWith('.tar.xz')) {
        await extractTar(archivePath, folderPath, 'xz');
    }
    else {
        throw new Error(`Unsupported archive format: ${archivePath}`);
    }
}
function createTransformStream(child) {
    const stream = new node_stream_1.Stream.Transform({
        transform(chunk, encoding, callback) {
            if (!child.stdin.write(chunk, encoding)) {
                child.stdin.once('drain', callback);
            }
            else {
                callback();
            }
        },
        flush(callback) {
            if (child.stdout.destroyed) {
                callback();
            }
            else {
                child.stdin.end();
                child.stdout.on('close', callback);
            }
        },
    });
    child.stdin.on('error', e => {
        if ('code' in e && e.code === 'EPIPE') {
            // finished before reading the file finished (i.e. head)
            stream.emit('end');
        }
        else {
            stream.destroy(e);
        }
    });
    child.stdout
        .on('data', data => {
        return stream.push(data);
    })
        .on('error', e => {
        return stream.destroy(e);
    });
    child.once('close', () => {
        return stream.end();
    });
    return stream;
}
/**
 * @internal
 */
exports.internalConstantsForTesting = {
    xz: 'xz',
    bzip2: 'bzip2',
};
/**
 * @internal
 */
async function extractTar(tarPath, folderPath, decompressUtilityName) {
    const tarFs = await import('tar-fs');
    return await new Promise((fulfill, reject) => {
        function handleError(utilityName) {
            return (error) => {
                if ('code' in error && error.code === 'ENOENT') {
                    error = new Error(`\`${utilityName}\` utility is required to unpack this archive`, {
                        cause: error,
                    });
                }
                reject(error);
            };
        }
        const unpack = (0, node_child_process_1.spawn)(exports.internalConstantsForTesting[decompressUtilityName], ['-d'], {
            stdio: ['pipe', 'pipe', 'inherit'],
        })
            .once('error', handleError(decompressUtilityName))
            .once('exit', code => {
            debugFileUtil(`${decompressUtilityName} exited, code=${code}`);
        });
        const tar = tarFs.extract(folderPath);
        tar.once('error', handleError('tar'));
        tar.once('finish', fulfill);
        (0, node_fs_1.createReadStream)(tarPath).pipe(createTransformStream(unpack)).pipe(tar);
    });
}
/**
 * @internal
 */
async function installDMG(dmgPath, folderPath) {
    const { stdout } = (0, node_child_process_1.spawnSync)(`hdiutil`, [
        'attach',
        '-nobrowse',
        '-noautoopen',
        dmgPath,
    ]);
    const volumes = stdout.toString('utf8').match(/\/Volumes\/(.*)/m);
    if (!volumes) {
        throw new Error(`Could not find volume path in ${stdout}`);
    }
    const mountPath = volumes[0];
    try {
        const fileNames = await (0, promises_1.readdir)(mountPath);
        const appName = fileNames.find(item => {
            return typeof item === 'string' && item.endsWith('.app');
        });
        if (!appName) {
            throw new Error(`Cannot find app in ${mountPath}`);
        }
        const mountedPath = path.join(mountPath, appName);
        (0, node_child_process_1.spawnSync)('cp', ['-R', mountedPath, folderPath]);
    }
    finally {
        (0, node_child_process_1.spawnSync)('hdiutil', ['detach', mountPath, '-quiet']);
    }
}
//# sourceMappingURL=fileUtil.js.map