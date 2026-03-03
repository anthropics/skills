"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.testLine = testLine;
exports.parseLine = parseLine;
exports.transformList = transformList;
const FileInfo_1 = require("./FileInfo");
/**
 * This parser is based on the FTP client library source code in Apache Commons Net provided
 * under the Apache 2.0 license. It has been simplified and rewritten to better fit the Javascript language.
 *
 * https://github.com/apache/commons-net/blob/master/src/main/java/org/apache/commons/net/ftp/parser/NTFTPEntryParser.java
 */
const RE_LINE = new RegExp("(\\S+)\\s+(\\S+)\\s+" // MM-dd-yy whitespace hh:mma|kk:mm swallow trailing spaces
    + "(?:(<DIR>)|([0-9]+))\\s+" // <DIR> or ddddd swallow trailing spaces
    + "(\\S.*)" // First non-space followed by rest of line (name)
);
/**
 * Returns true if a given line might be a DOS-style listing.
 *
 * - Example: `12-05-96  05:03PM       <DIR>          myDir`
 */
function testLine(line) {
    return /^\d{2}/.test(line) && RE_LINE.test(line);
}
/**
 * Parse a single line of a DOS-style directory listing.
 */
function parseLine(line) {
    const groups = line.match(RE_LINE);
    if (groups === null) {
        return undefined;
    }
    const name = groups[5];
    if (name === "." || name === "..") { // Ignore parent directory links
        return undefined;
    }
    const file = new FileInfo_1.FileInfo(name);
    const fileType = groups[3];
    if (fileType === "<DIR>") {
        file.type = FileInfo_1.FileType.Directory;
        file.size = 0;
    }
    else {
        file.type = FileInfo_1.FileType.File;
        file.size = parseInt(groups[4], 10);
    }
    file.rawModifiedAt = groups[1] + " " + groups[2];
    return file;
}
function transformList(files) {
    return files;
}
