"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.testLine = testLine;
exports.parseLine = parseLine;
exports.transformList = transformList;
const FileInfo_1 = require("./FileInfo");
const JA_MONTH = "\u6708";
const JA_DAY = "\u65e5";
const JA_YEAR = "\u5e74";
/**
 * This parser is based on the FTP client library source code in Apache Commons Net provided
 * under the Apache 2.0 license. It has been simplified and rewritten to better fit the Javascript language.
 *
 * https://github.com/apache/commons-net/blob/master/src/main/java/org/apache/commons/net/ftp/parser/UnixFTPEntryParser.java
 *
 * Below is the regular expression used by this parser.
 *
 * Permissions:
 *    r   the file is readable
 *    w   the file is writable
 *    x   the file is executable
 *    -   the indicated permission is not granted
 *    L   mandatory locking occurs during access (the set-group-ID bit is
 *        on and the group execution bit is off)
 *    s   the set-user-ID or set-group-ID bit is on, and the corresponding
 *        user or group execution bit is also on
 *    S   undefined bit-state (the set-user-ID bit is on and the user
 *        execution bit is off)
 *    t   the 1000 (octal) bit, or sticky bit, is on [see chmod(1)], and
 *        execution is on
 *    T   the 1000 bit is turned on, and execution is off (undefined bit-
 *        state)
 *    e   z/OS external link bit
 *    Final letter may be appended:
 *    +   file has extended security attributes (e.g. ACL)
 *    Note: local listings on MacOSX also use '@'
 *    this is not allowed for here as does not appear to be shown by FTP servers
 *    {@code @}   file has extended attributes
 */
const RE_LINE = new RegExp("([bcdelfmpSs-])" // file type
    + "(((r|-)(w|-)([xsStTL-]))((r|-)(w|-)([xsStTL-]))((r|-)(w|-)([xsStTL-]?)))\\+?" // permissions
    + "\\s*" // separator TODO why allow it to be omitted??
    + "(\\d+)" // link count
    + "\\s+" // separator
    + "(?:(\\S+(?:\\s\\S+)*?)\\s+)?" // owner name (optional spaces)
    + "(?:(\\S+(?:\\s\\S+)*)\\s+)?" // group name (optional spaces)
    + "(\\d+(?:,\\s*\\d+)?)" // size or n,m
    + "\\s+" // separator
    /**
     * numeric or standard format date:
     *   yyyy-mm-dd (expecting hh:mm to follow)
     *   MMM [d]d
     *   [d]d MMM
     *   N.B. use non-space for MMM to allow for languages such as German which use
     *   diacritics (e.g. umlaut) in some abbreviations.
     *   Japanese uses numeric day and month with suffixes to distinguish them
     *   [d]dXX [d]dZZ
     */
    + "(" +
    "(?:\\d+[-/]\\d+[-/]\\d+)" + // yyyy-mm-dd
    "|(?:\\S{3}\\s+\\d{1,2})" + // MMM [d]d
    "|(?:\\d{1,2}\\s+\\S{3})" + // [d]d MMM
    "|(?:\\d{1,2}" + JA_MONTH + "\\s+\\d{1,2}" + JA_DAY + ")" +
    ")"
    + "\\s+" // separator
    /**
     * year (for non-recent standard format) - yyyy
     * or time (for numeric or recent standard format) [h]h:mm
     * or Japanese year - yyyyXX
     */
    + "((?:\\d+(?::\\d+)?)|(?:\\d{4}" + JA_YEAR + "))" // (20)
    + "\\s" // separator
    + "(.*)"); // the rest (21)
/**
 * Returns true if a given line might be a Unix-style listing.
 *
 * - Example: `-rw-r--r--+   1 patrick  staff   1057 Dec 11 14:35 test.txt`
 */
function testLine(line) {
    return RE_LINE.test(line);
}
/**
 * Parse a single line of a Unix-style directory listing.
 */
function parseLine(line) {
    const groups = line.match(RE_LINE);
    if (groups === null) {
        return undefined;
    }
    const name = groups[21];
    if (name === "." || name === "..") { // Ignore parent directory links
        return undefined;
    }
    const file = new FileInfo_1.FileInfo(name);
    file.size = parseInt(groups[18], 10);
    file.user = groups[16];
    file.group = groups[17];
    file.hardLinkCount = parseInt(groups[15], 10);
    file.rawModifiedAt = groups[19] + " " + groups[20];
    file.permissions = {
        user: parseMode(groups[4], groups[5], groups[6]),
        group: parseMode(groups[8], groups[9], groups[10]),
        world: parseMode(groups[12], groups[13], groups[14]),
    };
    // Set file type
    switch (groups[1].charAt(0)) {
        case "d":
            file.type = FileInfo_1.FileType.Directory;
            break;
        case "e": // NET-39 => z/OS external link
            file.type = FileInfo_1.FileType.SymbolicLink;
            break;
        case "l":
            file.type = FileInfo_1.FileType.SymbolicLink;
            break;
        case "b":
        case "c":
            file.type = FileInfo_1.FileType.File; // TODO change this if DEVICE_TYPE implemented
            break;
        case "f":
        case "-":
            file.type = FileInfo_1.FileType.File;
            break;
        default:
            // A 'whiteout' file is an ARTIFICIAL entry in any of several types of
            // 'translucent' filesystems, of which a 'union' filesystem is one.
            file.type = FileInfo_1.FileType.Unknown;
    }
    // Separate out the link name for symbolic links
    if (file.isSymbolicLink) {
        const end = name.indexOf(" -> ");
        if (end !== -1) {
            file.name = name.substring(0, end);
            file.link = name.substring(end + 4);
        }
    }
    return file;
}
function transformList(files) {
    return files;
}
function parseMode(r, w, x) {
    let value = 0;
    if (r !== "-") {
        value += FileInfo_1.FileInfo.UnixPermission.Read;
    }
    if (w !== "-") {
        value += FileInfo_1.FileInfo.UnixPermission.Write;
    }
    const execToken = x.charAt(0);
    if (execToken !== "-" && execToken.toUpperCase() !== execToken) {
        value += FileInfo_1.FileInfo.UnixPermission.Execute;
    }
    return value;
}
