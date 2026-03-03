"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.parseControlResponse = parseControlResponse;
exports.isSingleLine = isSingleLine;
exports.isMultiline = isMultiline;
exports.positiveCompletion = positiveCompletion;
exports.positiveIntermediate = positiveIntermediate;
const LF = "\n";
/**
 * Parse an FTP control response as a collection of messages. A message is a complete
 * single- or multiline response. A response can also contain multiple multiline responses
 * that will each be represented by a message. A response can also be incomplete
 * and be completed on the next incoming data chunk for which case this function also
 * describes a `rest`. This function converts all CRLF to LF.
 */
function parseControlResponse(text) {
    const lines = text.split(/\r?\n/).filter(isNotBlank);
    const messages = [];
    let startAt = 0;
    let tokenRegex;
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        // No group has been opened.
        if (!tokenRegex) {
            if (isMultiline(line)) {
                // Open a group by setting an expected token.
                const token = line.substr(0, 3);
                tokenRegex = new RegExp(`^${token}(?:$| )`);
                startAt = i;
            }
            else if (isSingleLine(line)) {
                // Single lines can be grouped immediately.
                messages.push(line);
            }
        }
        // Group has been opened, expect closing token.
        else if (tokenRegex.test(line)) {
            tokenRegex = undefined;
            messages.push(lines.slice(startAt, i + 1).join(LF));
        }
    }
    // The last group might not have been closed, report it as a rest.
    const rest = tokenRegex ? lines.slice(startAt).join(LF) + LF : "";
    return { messages, rest };
}
function isSingleLine(line) {
    return /^\d\d\d(?:$| )/.test(line);
}
function isMultiline(line) {
    return /^\d\d\d-/.test(line);
}
/**
 * Return true if an FTP return code describes a positive completion.
 */
function positiveCompletion(code) {
    return code >= 200 && code < 300;
}
/**
 * Return true if an FTP return code describes a positive intermediate response.
 */
function positiveIntermediate(code) {
    return code >= 300 && code < 400;
}
function isNotBlank(str) {
    return str.trim() !== "";
}
