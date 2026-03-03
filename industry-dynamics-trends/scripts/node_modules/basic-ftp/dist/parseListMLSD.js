"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.testLine = testLine;
exports.parseLine = parseLine;
exports.transformList = transformList;
exports.parseMLSxDate = parseMLSxDate;
const FileInfo_1 = require("./FileInfo");
function parseSize(value, info) {
    info.size = parseInt(value, 10);
}
/**
 * Parsers for MLSD facts.
 */
const factHandlersByName = {
    "size": parseSize, // File size
    "sizd": parseSize, // Directory size
    "unique": (value, info) => {
        info.uniqueID = value;
    },
    "modify": (value, info) => {
        info.modifiedAt = parseMLSxDate(value);
        info.rawModifiedAt = info.modifiedAt.toISOString();
    },
    "type": (value, info) => {
        // There seems to be confusion on how to handle symbolic links for Unix. RFC 3659 doesn't describe
        // this but mentions some examples using the syntax `type=OS.unix=slink:<target>`. But according to
        // an entry in the Errata (https://www.rfc-editor.org/errata/eid1500) this syntax can't be valid.
        // Instead it proposes to use `type=OS.unix=symlink` and to then list the actual target of the
        // symbolic link as another entry in the directory listing. The unique identifiers can then be used
        // to derive the connection between link(s) and target. We'll have to handle both cases as there
        // are differing opinions on how to deal with this. Here are some links on this topic:
        // - ProFTPD source: https://github.com/proftpd/proftpd/blob/56e6dfa598cbd4ef5c6cba439bcbcd53a63e3b21/modules/mod_facts.c#L531
        // - ProFTPD bug: http://bugs.proftpd.org/show_bug.cgi?id=3318
        // - ProFTPD statement: http://www.proftpd.org/docs/modules/mod_facts.html
        // – FileZilla bug: https://trac.filezilla-project.org/ticket/9310
        if (value.startsWith("OS.unix=slink")) {
            info.type = FileInfo_1.FileType.SymbolicLink;
            info.link = value.substr(value.indexOf(":") + 1);
            return 1 /* FactHandlerResult.Continue */;
        }
        switch (value) {
            case "file":
                info.type = FileInfo_1.FileType.File;
                break;
            case "dir":
                info.type = FileInfo_1.FileType.Directory;
                break;
            case "OS.unix=symlink":
                info.type = FileInfo_1.FileType.SymbolicLink;
                // The target of the symbolic link might be defined in another line in the directory listing.
                // We'll handle this in `transformList()` below.
                break;
            case "cdir": // Current directory being listed
            case "pdir": // Parent directory
                return 2 /* FactHandlerResult.IgnoreFile */; // Don't include these entries in the listing
            default:
                info.type = FileInfo_1.FileType.Unknown;
        }
        return 1 /* FactHandlerResult.Continue */;
    },
    "unix.mode": (value, info) => {
        const digits = value.substr(-3);
        info.permissions = {
            user: parseInt(digits[0], 10),
            group: parseInt(digits[1], 10),
            world: parseInt(digits[2], 10)
        };
    },
    "unix.ownername": (value, info) => {
        info.user = value;
    },
    "unix.owner": (value, info) => {
        if (info.user === undefined)
            info.user = value;
    },
    get "unix.uid"() {
        return this["unix.owner"];
    },
    "unix.groupname": (value, info) => {
        info.group = value;
    },
    "unix.group": (value, info) => {
        if (info.group === undefined)
            info.group = value;
    },
    get "unix.gid"() {
        return this["unix.group"];
    }
    // Regarding the fact "perm":
    // We don't handle permission information stored in "perm" because its information is conceptually
    // different from what users of FTP clients usually associate with "permissions". Those that have
    // some expectations (and probably want to edit them with a SITE command) often unknowingly expect
    // the Unix permission system. The information passed by "perm" describes what FTP commands can be
    // executed with a file/directory. But even this can be either incomplete or just meant as a "guide"
    // as the spec mentions. From https://tools.ietf.org/html/rfc3659#section-7.5.5: "The permissions are
    // described here as they apply to FTP commands. They may not map easily into particular permissions
    // available on the server's operating system." The parser by Apache Commons tries to translate these
    // to Unix permissions – this is misleading users and might not even be correct.
};
/**
 * Split a string once at the first position of a delimiter. For example
 * `splitStringOnce("a b c d", " ")` returns `["a", "b c d"]`.
 */
function splitStringOnce(str, delimiter) {
    const pos = str.indexOf(delimiter);
    const a = str.substr(0, pos);
    const b = str.substr(pos + delimiter.length);
    return [a, b];
}
/**
 * Returns true if a given line might be part of an MLSD listing.
 *
 * - Example 1: `size=15227;type=dir;perm=el;modify=20190419065730; test one`
 * - Example 2: ` file name` (leading space)
 */
function testLine(line) {
    return /^\S+=\S+;/.test(line) || line.startsWith(" ");
}
/**
 * Parse single line as MLSD listing, see specification at https://tools.ietf.org/html/rfc3659#section-7.
 */
function parseLine(line) {
    const [packedFacts, name] = splitStringOnce(line, " ");
    if (name === "" || name === "." || name === "..") {
        return undefined;
    }
    const info = new FileInfo_1.FileInfo(name);
    const facts = packedFacts.split(";");
    for (const fact of facts) {
        const [factName, factValue] = splitStringOnce(fact, "=");
        if (!factValue) {
            continue;
        }
        const factHandler = factHandlersByName[factName.toLowerCase()];
        if (!factHandler) {
            continue;
        }
        const result = factHandler(factValue, info);
        if (result === 2 /* FactHandlerResult.IgnoreFile */) {
            return undefined;
        }
    }
    return info;
}
function transformList(files) {
    // Create a map of all files that are not symbolic links by their unique ID
    const nonLinksByID = new Map();
    for (const file of files) {
        if (!file.isSymbolicLink && file.uniqueID !== undefined) {
            nonLinksByID.set(file.uniqueID, file);
        }
    }
    const resolvedFiles = [];
    for (const file of files) {
        // Try to associate unresolved symbolic links with a target file/directory.
        if (file.isSymbolicLink && file.uniqueID !== undefined && file.link === undefined) {
            const target = nonLinksByID.get(file.uniqueID);
            if (target !== undefined) {
                file.link = target.name;
            }
        }
        // The target of a symbolic link is listed as an entry in the directory listing but might
        // have a path pointing outside of this directory. In that case we don't want this entry
        // to be part of the listing. We generally don't want these kind of entries at all.
        const isPartOfDirectory = !file.name.includes("/");
        if (isPartOfDirectory) {
            resolvedFiles.push(file);
        }
    }
    return resolvedFiles;
}
/**
 * Parse date as specified in https://tools.ietf.org/html/rfc3659#section-2.3.
 *
 * Message contains response code and modified time in the format: YYYYMMDDHHMMSS[.sss]
 * For example `19991005213102` or `19980615100045.014`.
 */
function parseMLSxDate(fact) {
    return new Date(Date.UTC(+fact.slice(0, 4), // Year
    +fact.slice(4, 6) - 1, // Month
    +fact.slice(6, 8), // Date
    +fact.slice(8, 10), // Hours
    +fact.slice(10, 12), // Minutes
    +fact.slice(12, 14), // Seconds
    +fact.slice(15, 18) // Milliseconds
    ));
}
