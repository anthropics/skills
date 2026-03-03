"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.FileInfo = exports.FileType = void 0;
var FileType;
(function (FileType) {
    FileType[FileType["Unknown"] = 0] = "Unknown";
    FileType[FileType["File"] = 1] = "File";
    FileType[FileType["Directory"] = 2] = "Directory";
    FileType[FileType["SymbolicLink"] = 3] = "SymbolicLink";
})(FileType || (exports.FileType = FileType = {}));
/**
 * Describes a file, directory or symbolic link.
 */
class FileInfo {
    constructor(name) {
        this.name = name;
        this.type = FileType.Unknown;
        this.size = 0;
        /**
         * Unparsed, raw modification date as a string.
         *
         * If `modifiedAt` is undefined, the FTP server you're connected to doesn't support the more modern
         * MLSD command for machine-readable directory listings. The older command LIST is then used returning
         * results that vary a lot between servers as the format hasn't been standardized. Here, directory listings
         * and especially modification dates were meant to be human-readable first.
         *
         * Be careful when still trying to parse this by yourself. Parsing dates from listings using LIST is
         * unreliable. This library decides to offer parsed dates only when they're absolutely reliable and safe to
         * use e.g. for comparisons.
         */
        this.rawModifiedAt = "";
        /**
         * Parsed modification date.
         *
         * Available if the FTP server supports the MLSD command. Only MLSD guarantees dates than can be reliably
         * parsed with the correct timezone and a resolution down to seconds. See `rawModifiedAt` property for the unparsed
         * date that is always available.
         */
        this.modifiedAt = undefined;
        /**
         * Unix permissions if present. If the underlying FTP server is not running on Unix this will be undefined.
         * If set, you might be able to edit permissions with the FTP command `SITE CHMOD`.
         */
        this.permissions = undefined;
        /**
         * Hard link count if available.
         */
        this.hardLinkCount = undefined;
        /**
         * Link name for symbolic links if available.
         */
        this.link = undefined;
        /**
         * Unix group if available.
         */
        this.group = undefined;
        /**
         * Unix user if available.
         */
        this.user = undefined;
        /**
         * Unique ID if available.
         */
        this.uniqueID = undefined;
        this.name = name;
    }
    get isDirectory() {
        return this.type === FileType.Directory;
    }
    get isSymbolicLink() {
        return this.type === FileType.SymbolicLink;
    }
    get isFile() {
        return this.type === FileType.File;
    }
    /**
     * Deprecated, legacy API. Use `rawModifiedAt` instead.
     * @deprecated
     */
    get date() {
        return this.rawModifiedAt;
    }
    set date(rawModifiedAt) {
        this.rawModifiedAt = rawModifiedAt;
    }
}
exports.FileInfo = FileInfo;
FileInfo.UnixPermission = {
    Read: 4,
    Write: 2,
    Execute: 1
};
