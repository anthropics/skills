// Based on the type definitions for extract-zip 1.6
// Definitions by: Mizunashi Mana <https://github.com/mizunashi-mana>
// Definitions: https://github.com/DefinitelyTyped/DefinitelyTyped/blob/e69b58e/types/extract-zip/index.d.ts

import { Entry, ZipFile } from 'yauzl';

declare namespace extract {
    interface Options {
        dir: string;
        defaultDirMode?: number;
        defaultFileMode?: number;
        onEntry?: (entry: Entry, zipfile: ZipFile) => void;
    }
}

declare function extract(
  zipPath: string,
  opts: extract.Options,
): Promise<void>;

export = extract;
