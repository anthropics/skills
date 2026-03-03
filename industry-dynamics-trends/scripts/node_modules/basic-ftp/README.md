# Basic FTP

[![npm version](https://img.shields.io/npm/v/basic-ftp.svg)](https://www.npmjs.com/package/basic-ftp)
[![npm downloads](https://img.shields.io/npm/dw/basic-ftp)](https://www.npmjs.com/package/basic-ftp)
[![Node.js CI](https://github.com/patrickjuchli/basic-ftp/actions/workflows/nodejs.yml/badge.svg)](https://github.com/patrickjuchli/basic-ftp/actions/workflows/nodejs.yml)

This is an FTP client library for Node.js. It supports FTPS over TLS, Passive Mode over IPv6, has a Promise-based API, and offers methods to operate on whole directories. Active Mode is not supported.

## Advisory

Prefer alternative transfer protocols like HTTPS or SFTP (SSH). FTP is a an old protocol with some reliability issues. Use this library when you have no choice and need to use FTP. Try to use FTPS (FTP over TLS) whenever possible, FTP alone does not provide any security.

## Dependencies

Node 10.0 or later is the only dependency.

## Installation

`npm install basic-ftp`

## Usage

The first example will connect to an FTP server using TLS (FTPS), get a directory listing, upload a file and download it as a copy. Note that the FTP protocol doesn't allow multiple requests running in parallel.

```js
const { Client } = require("basic-ftp") 
// ESM: import { Client } from "basic-ftp"

example()

async function example() {
    const client = new Client()
    client.ftp.verbose = true
    try {
        await client.access({
            host: "myftpserver.com",
            user: "very",
            password: "password",
            secure: true
        })
        console.log(await client.list())
        await client.uploadFrom("README.md", "README_FTP.md")
        await client.downloadTo("README_COPY.md", "README_FTP.md")
    }
    catch(err) {
        console.log(err)
    }
    client.close()
}
```

The next example deals with directories and their content. First, we make sure a remote path exists, creating all directories as necessary. Then, we make sure it's empty and upload the contents of a local directory.

```js
await client.ensureDir("my/remote/directory")
await client.clearWorkingDir()
await client.uploadFromDir("my/local/directory")
```

If you encounter a problem, it may help to log out all communication with the FTP server.

```js
client.ftp.verbose = true
```

## Client API

`new Client(timeout, options)`

Create a client instance. Configure it with a timeout in milliseconds that will be used for any connection made. Use 0 to disable timeouts, default is 30 seconds. Options are: 

- `allowSeparateTransferHost (boolean)`, the FTP spec makes it possible for a server to tell the client to use a different IP address for file transfers than for the initial control connection. Today, this feature is very rarely used. Still, the default for this is set to `true` for backwards-compatibility reasons. If you experience any issues with NAT traversal in local networks or want to provide more security and prevent FTP bounce attacks, set this to `false`.

`close()`

Close the client and any open connection. The client can’t be used anymore after calling this method, you'll have to reconnect with `access` to continue any work. A client is also closed automatically if any timeout or connection error occurs. See the section on [Error Handling](#error-handling) below.

`closed`

True if the client is not connected to a server. You can reconnect with `access`.

`access(options): Promise<FTPResponse>`

Get access to an FTP server. This method will connect to a server, optionally secure the connection with TLS, login a user and apply some default settings (TYPE I, STRU F, PBSZ 0, PROT P). It returns the response of the initial connect command. This is an instance method and thus can be called multiple times during the lifecycle of a `Client` instance. Whenever you do, the client is reset with a new connection. This also implies that you can reopen a `Client` instance that has been closed due to an error when reconnecting with this method. The available options are:

- `host (string)` Server host, default: localhost
- `port (number)` Server port, default: 21
- `user (string)` Username, default: anonymous
- `password (string)` Password, default: guest
- `secure (boolean | "implicit")` Explicit FTPS over TLS, default: false. Use "implicit" if you need support for legacy implicit FTPS.
- `secureOptions` Options for TLS, same as for [tls.connect()](https://nodejs.org/api/tls.html#tls_tls_connect_options_callback) in Node.js.

---

`features(): Promise<Map<string, string>>`

Get a description of supported features. This will return a Map where keys correspond to FTP commands and values contain further details. If the FTP server doesn't support this request you'll still get an empty Map instead of an error response.

`send(command): Promise<FTPResponse>`

Send an FTP command and return the first response.

`sendIgnoringError(command): Promise<FTPResponse>`

Send an FTP command, return the first response, and ignore an FTP error response. Any other error or timeout will still reject the Promise.

`cd(path): Promise<FTPResponse>`

Change the current working directory.

`pwd(): Promise<string>`

Get the path of the current working directory.

`list([path]): Promise<FileInfo[]>`

List files and directories in the current working directory, or at `path` if specified. Currently, this library only supports MLSD, Unix and DOS directory listings. See [FileInfo](src/FileInfo.ts) for more details.

`lastMod(path): Promise<Date>`

Get the last modification time of a file. This command might not be supported by your FTP server and throw an exception.

`size(path): Promise<number>`

Get the size of a file in bytes.

`rename(path, newPath): Promise<FTPResponse>`

Rename a file. Depending on the server you may also use this to move a file to another directory by providing full paths.

`remove(path): Promise<FTPResponse>`

Remove a file.

`uploadFrom(readableStream | localPath, remotePath, [options]): Promise<FTPResponse>`

Upload data from a readable stream or a local file to a remote file. If such a file already exists it will be overwritten. If a file is being uploaded, additional options offer `localStart` and `localEndInclusive` to only upload parts of it.

`appendFrom(readableStream | localPath, remotePath, [options]): Promise<FTPResponse>`

Upload data from a readable stream or a local file by appending it to an existing file. If the file doesn't exist the FTP server should create it. If a file is being uploaded, additional options offer `localStart` and `localEndInclusive` to only upload parts of it. For example: To resume a failed upload, request the size of the remote, partially uploaded file using `size()` and use it as `localStart`.

`downloadTo(writableStream | localPath, remotePath, startAt = 0): Promise<FTPResponse>`

Download a remote file and pipe its data to a writable stream or to a local file. You can optionally define at which position of the remote file you'd like to start downloading. If the destination you provide is a file, the offset will be applied to it as well. For example: To resume a failed download, request the size of the local, partially downloaded file and use that as `startAt`.

---

`ensureDir(remoteDirPath): Promise<void>`

Make sure that the given `remoteDirPath` exists on the server, creating all directories as necessary. The working directory is at `remoteDirPath` after calling this method.

`clearWorkingDir(): Promise<void>`

Remove all files and directories from the working directory.

`removeDir(remoteDirPath): Promise<void>`

Remove all files and directories from a given directory, including the directory itself. The working directory stays the same unless it is part of the deleted directories.

`uploadFromDir(localDirPath, [remoteDirPath]): Promise<void>`

Upload the contents of a local directory to the current remote working directory. This will overwrite existing files with the same names and reuse existing directories. Unrelated files and directories will remain untouched. You can optionally provide a `remoteDirPath` to put the contents inside any remote directory which will be created if necessary including all intermediate directories. The working directory stays the same after calling this method.

`downloadToDir(localDirPath, [remoteDirPath]): Promise<void>`

Download all files and directories of the current working directory to a given local directory. You can optionally set a specific remote directory. The working directory stays the same after calling this method.

---

`trackProgress(handler)`

Report any transfer progress using the given handler function. See the next section for more details.

## Transfer Progress

Set a callback function with `client.trackProgress` to track the progress of any transfer. Transfers are uploads, downloads or directory listings. To disable progress reporting, call `trackProgress` without a handler.

```js
// Log progress for any transfer from now on.
client.trackProgress(info => {
    console.log("File", info.name)
    console.log("Type", info.type)
    console.log("Transferred", info.bytes)
    console.log("Transferred Overall", info.bytesOverall)
})

// Transfer some data
await client.uploadFrom(someStream, "test.txt")
await client.uploadFrom("somefile.txt", "test2.txt")

// Set a new callback function which also resets the overall counter
client.trackProgress(info => console.log(info.bytesOverall))
await client.downloadToDir("local/path", "remote/path")

// Stop logging
client.trackProgress()
```

For each transfer, the callback function will receive the filename, transfer type (`upload`, `download` or `list`) and number of bytes transferred. The function will be called at a regular interval during a transfer.

There is also a counter for all bytes transferred since the last time `trackProgress` was called. This is useful when downloading a directory with multiple files where you want to show the total bytes downloaded so far.

## Error Handling

Any error reported by the FTP server will be thrown as `FTPError`. The connection to the FTP server stays intact and you can continue to use your `Client` instance.

This is different with a timeout or connection error: In addition to an `Error` being thrown, any connection to the FTP server will be closed. You’ll have to reconnect with `client.access()`, if you want to continue any work.

## Logging

Using `client.ftp.verbose = true` will log debug-level information to the console. You can use your own logging library by overriding `client.ftp.log`. This method is called regardless of what `client.ftp.verbose` is set to. For example:

```
myClient.ftp.log = myLogger.debug
```

## Static Types

In addition to unit tests and linting, the source code is written in Typescript using rigorous [compiler settings](tsconfig.json) like `strict` and `noImplicitAny`. When building the project, the source is transpiled to Javascript and type declaration files. This makes the library useable for both Javascript and Typescript projects.

## Extending the library

### Client

`get/set client.parseList`

Provide a function to parse directory listing data. This library supports MLSD, Unix and DOS formats. Parsing these list responses is one of the more challenging parts of FTP because there is no standard that all servers adhere to. The signature of the function is `(rawList: string) => FileInfo[]`.

### FTPContext

The Client API described so far is implemented using an FTPContext. An FTPContext provides the foundation to write an FTP client. It holds the socket connections and provides an API to handle responses and events in a simplified way. Through `client.ftp` you get access to this context.

`get/set verbose`

Set the verbosity level to optionally log out all communication between the client and the server.

`get/set encoding`

Set the encoding applied to all incoming and outgoing messages of the control connection. This encoding is also used when parsing a list response from a data connection. See https://nodejs.org/api/buffer.html#buffer_buffers_and_character_encodings for what encodings are supported by Node.js. Default is `utf8` because most modern servers support it, some of them without mentioning it when requesting features.

## Acknowledgment

This library uses parts of the [directory listing parsers](https://github.com/apache/commons-net/tree/master/src/main/java/org/apache/commons/net/ftp/parser) written by The Apache Software Foundation. They've been made available under the Apache 2.0 license. See the [included notice](NOTICE.txt) and headers in the respective files containing the original copyright texts and a description of changes.
