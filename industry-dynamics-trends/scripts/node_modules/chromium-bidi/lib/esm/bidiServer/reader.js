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
 */
import fs from 'fs/promises';
import path from 'path';
import url from 'url';
const __dirname = url.fileURLToPath(new URL('.', import.meta.url));
export async function getMapperTabSource() {
    return await fs.readFile(path.join(__dirname, '../../iife/mapperTab.js'), 'utf8');
}
//
//# sourceMappingURL=reader.js.map