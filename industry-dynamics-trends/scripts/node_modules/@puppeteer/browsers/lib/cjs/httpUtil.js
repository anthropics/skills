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
Object.defineProperty(exports, "__esModule", { value: true });
exports.headHttpRequest = headHttpRequest;
exports.httpRequest = httpRequest;
exports.downloadFile = downloadFile;
exports.getJSON = getJSON;
exports.getText = getText;
const node_fs_1 = require("node:fs");
const http = __importStar(require("node:http"));
const https = __importStar(require("node:https"));
const node_url_1 = require("node:url");
const proxy_agent_1 = require("proxy-agent");
function headHttpRequest(url) {
    return new Promise(resolve => {
        const request = httpRequest(url, 'HEAD', response => {
            // consume response data free node process
            response.resume();
            resolve(response.statusCode === 200);
        }, false);
        request.on('error', () => {
            resolve(false);
        });
    });
}
function httpRequest(url, method, response, keepAlive = true) {
    const options = {
        protocol: url.protocol,
        hostname: url.hostname,
        port: url.port,
        path: url.pathname + url.search,
        method,
        headers: keepAlive ? { Connection: 'keep-alive' } : undefined,
        auth: (0, node_url_1.urlToHttpOptions)(url).auth,
        agent: new proxy_agent_1.ProxyAgent(),
    };
    const requestCallback = (res) => {
        if (res.statusCode &&
            res.statusCode >= 300 &&
            res.statusCode < 400 &&
            res.headers.location) {
            httpRequest(new node_url_1.URL(res.headers.location), method, response);
            // consume response data to free up memory
            // And prevents the connection from being kept alive
            res.resume();
        }
        else {
            response(res);
        }
    };
    const request = options.protocol === 'https:'
        ? https.request(options, requestCallback)
        : http.request(options, requestCallback);
    request.end();
    return request;
}
/**
 * @internal
 */
function downloadFile(url, destinationPath, progressCallback) {
    return new Promise((resolve, reject) => {
        let downloadedBytes = 0;
        let totalBytes = 0;
        function onData(chunk) {
            downloadedBytes += chunk.length;
            progressCallback(downloadedBytes, totalBytes);
        }
        const request = httpRequest(url, 'GET', response => {
            if (response.statusCode !== 200) {
                const error = new Error(`Download failed: server returned code ${response.statusCode}. URL: ${url}`);
                // consume response data to free up memory
                response.resume();
                reject(error);
                return;
            }
            const file = (0, node_fs_1.createWriteStream)(destinationPath);
            file.on('close', () => {
                // The 'close' event is emitted when the stream and any of its
                // underlying resources (a file descriptor, for example) have been
                // closed. The event indicates that no more events will be emitted, and
                // no further computation will occur.
                return resolve();
            });
            file.on('error', error => {
                // The 'error' event may be emitted by a Readable implementation at any
                // time. Typically, this may occur if the underlying stream is unable to
                // generate data due to an underlying internal failure, or when a stream
                // implementation attempts to push an invalid chunk of data.
                return reject(error);
            });
            response.pipe(file);
            totalBytes = parseInt(response.headers['content-length'], 10);
            if (progressCallback) {
                response.on('data', onData);
            }
        });
        request.on('error', error => {
            return reject(error);
        });
    });
}
async function getJSON(url) {
    const text = await getText(url);
    try {
        return JSON.parse(text);
    }
    catch {
        throw new Error('Could not parse JSON from ' + url.toString());
    }
}
function getText(url) {
    return new Promise((resolve, reject) => {
        const request = httpRequest(url, 'GET', response => {
            let data = '';
            if (response.statusCode && response.statusCode >= 400) {
                return reject(new Error(`Got status code ${response.statusCode}`));
            }
            response.on('data', chunk => {
                data += chunk;
            });
            response.on('end', () => {
                try {
                    return resolve(String(data));
                }
                catch {
                    return reject(new Error(`Failed to read text response from ${url}`));
                }
            });
        }, false);
        request.on('error', err => {
            reject(err);
        });
    });
}
//# sourceMappingURL=httpUtil.js.map