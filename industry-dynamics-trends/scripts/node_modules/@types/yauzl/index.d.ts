/// <reference types="node" />

import { EventEmitter } from "events";
import { Readable } from "stream";

export abstract class RandomAccessReader extends EventEmitter {
    _readStreamForRange(start: number, end: number): void;
    createReadStream(options: { start: number; end: number }): void;
    read(buffer: Buffer, offset: number, length: number, position: number, callback: (err: Error | null) => void): void;
    close(callback: (err: Error | null) => void): void;
}

export class Entry {
    comment: string;
    compressedSize: number;
    compressionMethod: number;
    crc32: number;
    externalFileAttributes: number;
    extraFieldLength: number;
    extraFields: Array<{ id: number; data: Buffer }>;
    fileCommentLength: number;
    fileName: string;
    fileNameLength: number;
    generalPurposeBitFlag: number;
    internalFileAttributes: number;
    lastModFileDate: number;
    lastModFileTime: number;
    relativeOffsetOfLocalHeader: number;
    uncompressedSize: number;
    versionMadeBy: number;
    versionNeededToExtract: number;

    getLastModDate(): Date;
    isEncrypted(): boolean;
    isCompressed(): boolean;
}

export interface ZipFileOptions {
    decompress: boolean | null;
    decrypt: boolean | null;
    start: number | null;
    end: number | null;
}

export class ZipFile extends EventEmitter {
    autoClose: boolean;
    comment: string;
    decodeStrings: boolean;
    emittedError: boolean;
    entriesRead: number;
    entryCount: number;
    fileSize: number;
    isOpen: boolean;
    lazyEntries: boolean;
    readEntryCursor: boolean;
    validateEntrySizes: boolean;

    constructor(
        reader: RandomAccessReader,
        centralDirectoryOffset: number,
        fileSize: number,
        entryCount: number,
        comment: string,
        autoClose: boolean,
        lazyEntries: boolean,
        decodeStrings: boolean,
        validateEntrySizes: boolean,
    );

    openReadStream(
        entry: Entry,
        options: ZipFileOptions,
        callback: (err: Error | null, stream: Readable) => void,
    ): void;
    openReadStream(entry: Entry, callback: (err: Error | null, stream: Readable) => void): void;
    close(): void;
    readEntry(): void;
}

export interface Options {
    autoClose?: boolean | undefined;
    lazyEntries?: boolean | undefined;
    decodeStrings?: boolean | undefined;
    validateEntrySizes?: boolean | undefined;
    strictFileNames?: boolean | undefined;
}

export function open(path: string, options: Options, callback?: (err: Error | null, zipfile: ZipFile) => void): void;
export function open(path: string, callback?: (err: Error | null, zipfile: ZipFile) => void): void;
export function fromFd(fd: number, options: Options, callback?: (err: Error | null, zipfile: ZipFile) => void): void;
export function fromFd(fd: number, callback?: (err: Error | null, zipfile: ZipFile) => void): void;
export function fromBuffer(
    buffer: Buffer,
    options: Options,
    callback?: (err: Error | null, zipfile: ZipFile) => void,
): void;
export function fromBuffer(buffer: Buffer, callback?: (err: Error | null, zipfile: ZipFile) => void): void;
export function fromRandomAccessReader(
    reader: RandomAccessReader,
    totalSize: number,
    options: Options,
    callback: (err: Error | null, zipfile: ZipFile) => void,
): void;
export function fromRandomAccessReader(
    reader: RandomAccessReader,
    totalSize: number,
    callback: (err: Error | null, zipfile: ZipFile) => void,
): void;
export function dosDateTimeToDate(date: number, time: number): Date;
export function validateFileName(fileName: string): string | null;
