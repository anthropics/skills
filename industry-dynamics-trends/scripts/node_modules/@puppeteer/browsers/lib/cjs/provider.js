"use strict";
/**
 * @license
 * Copyright 2026 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.buildArchiveFilename = buildArchiveFilename;
/**
 * Utility function to build a standard archive filename.
 * @public
 */
function buildArchiveFilename(browser, platform, buildId, extension = 'zip') {
    return `${browser}-${platform}-${buildId}.${extension}`;
}
//# sourceMappingURL=provider.js.map