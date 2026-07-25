export function replaceQuotes(content: string): string {
  return content
    .replace(/"([^"]+)"/g, "\u201c$1\u201d")
    .replace(/「([^」]+)」/g, "\u201c$1\u201d");
}
