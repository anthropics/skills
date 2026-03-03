"use strict";
/**
 * Copyright 2021 Google LLC.
 * Copyright (c) Microsoft Corporation.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * @license
 */
Object.defineProperty(exports, "__esModule", { value: true });
const BidiMapper_js_1 = require("../bidiMapper/BidiMapper.js");
const CdpConnection_js_1 = require("../cdp/CdpConnection.js");
const log_js_1 = require("../utils/log.js");
const BidiParser_js_1 = require("./BidiParser.js");
const mapperTabPage_js_1 = require("./mapperTabPage.js");
const Transport_js_1 = require("./Transport.js");
(0, mapperTabPage_js_1.generatePage)();
const mapperTabToServerTransport = new Transport_js_1.WindowBidiTransport();
const cdpTransport = new Transport_js_1.WindowCdpTransport();
/**
 * A CdpTransport implementation that uses the window.cdp bindings
 * injected by Target.exposeDevToolsProtocol.
 */
const cdpConnection = new CdpConnection_js_1.MapperCdpConnection(cdpTransport, mapperTabPage_js_1.log);
/**
 * Launches the BiDi mapper instance.
 * @param {string} selfTargetId
 * @param options Mapper options. E.g. `acceptInsecureCerts`.
 */
async function runMapperInstance(selfTargetId) {
    // eslint-disable-next-line no-console
    console.log('Launching Mapper instance with selfTargetId:', selfTargetId);
    const bidiServer = await BidiMapper_js_1.BidiServer.createAndStart(mapperTabToServerTransport, cdpConnection, 
    /**
     * Create a Browser CDP Session per Mapper instance.
     */
    await cdpConnection.createBrowserSession(), selfTargetId, new BidiParser_js_1.BidiParser(), mapperTabPage_js_1.log);
    (0, mapperTabPage_js_1.log)(log_js_1.LogType.debugInfo, 'Mapper instance has been launched');
    return bidiServer;
}
/**
 * Set `window.runMapper` to a function which launches the BiDi mapper instance.
 * @param selfTargetId Needed to filter out info related to BiDi target.
 */
window.runMapperInstance = async (selfTargetId) => {
    await runMapperInstance(selfTargetId);
};
//# sourceMappingURL=bidiTab.js.map