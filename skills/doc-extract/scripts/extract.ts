import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";

import { decodeRtf, decodeXml } from "./decoders.mjs";

const SKILL_ROOT = dirname(dirname(new URL(import.meta.url).pathname));

// Allowlist, not the full environment: the extractors parse untrusted
// document bytes and `lit` is a third-party binary — neither needs the API
// keys or tokens the caller was launched with. (Same allowlist as the
// contracts server's bundled copy, servers/documents/src/extract.mjs.)
const CHILD_ENV = Object.fromEntries(
  [
    "PATH",
    "HOME",
    "USERPROFILE",
    "TMPDIR",
    "TMP",
    "TEMP",
    "SYSTEMROOT",
    "COMSPEC",
    "XDG_DATA_HOME",
    "XDG_CACHE_HOME",
    "TESSDATA_PREFIX",
    "LITEPARSE_PATH",
    "HTTP_PROXY",
    "HTTPS_PROXY",
    "NO_PROXY",
    "http_proxy",
    "https_proxy",
    "no_proxy",
  ]
    .filter((k) => process.env[k] !== undefined)
    .map((k) => [k, process.env[k]]),
);

export function resolveLit(roots: string[] = []): string | undefined {
  // Prefer the liteparse `lit` bin that `bun install` drops in node_modules
  // (this skill's, then any caller-supplied roots), then PATH.
  const candidates = [
    ...[SKILL_ROOT, ...roots].map((r) => join(r, "node_modules", ".bin", "lit")),
    "lit",
  ];
  return candidates.find(
    (p) => spawnSync(p, ["--version"], { stdio: "ignore", env: CHILD_ENV }).status === 0,
  );
}

export type Extracted = { text: string; method: "liteparse" | "pdftotext" };

export function extractWithMethod(
  lit: string | undefined,
  src: string,
  isPdf = /\.pdf$/i.test(src),
): Extracted | null {
  if (lit) {
    // OCR on by default; retry --no-ocr so text-layer extraction still lands if the OCR path fails.
    // --format json, not text: liteparse 2.x emits no page boundaries in text/markdown output,
    // so page anchors can only be rebuilt from the JSON pages array.
    for (const extra of [[], ["--no-ocr"]]) {
      const r = spawnSync(
        lit,
        ["parse", src, "--format", "json", "--max-pages", "2000", ...extra],
        {
          encoding: "utf8",
          maxBuffer: 256 * 1024 * 1024,
          env: CHILD_ENV,
        },
      );
      if (r.status !== 0 || !r.stdout.trim()) continue;
      try {
        const pages: { page: number; text: string }[] = JSON.parse(r.stdout).pages ?? [];
        const text = pages.map((p) => `\n\n=== [page ${p.page}] ===\n\n${p.text}`).join("");
        if (text.trim()) return { text, method: "liteparse" };
      } catch {
        // unparseable stdout — try the next variant, then the pdftotext fallback
      }
    }
  }
  // Only PDFs have a no-liteparse fallback.
  if (!isPdf) return null;
  // Fallback: pdftotext -layout, page-anchored via form-feed splits.
  const r = spawnSync("pdftotext", ["-layout", src, "-"], {
    encoding: "utf8",
    maxBuffer: 256 * 1024 * 1024,
    env: CHILD_ENV,
  });
  if (r.status !== 0) return null;
  return {
    text: r.stdout
      .split("\f")
      .map((page, i) => `\n\n=== [page ${i + 1}] ===\n\n${page}`)
      .join(""),
    method: "pdftotext",
  };
}

export function extract(
  lit: string | undefined,
  src: string,
  isPdf = /\.pdf$/i.test(src),
): string | null {
  return extractWithMethod(lit, src, isPdf)?.text ?? null;
}

// mime axis — must cover every extension the fhir server's CONTENT_TYPES
// registry can emit (servers/fhir/src/documents.ts)
const KIND_BY_MIME: Record<string, string> = {
  "application/pdf": "pdf",
  "application/vnd.openxmlformats-officedocument.wordprocessingml.document": "docx",
  "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet": "xlsx",
  "application/vnd.openxmlformats-officedocument.presentationml.presentation": "pptx",
  "application/msword": "doc",
  "application/rtf": "rtf",
  "text/rtf": "rtf",
  "text/plain": "txt",
  "text/markdown": "md",
  "text/html": "html",
  "text/xml": "xml",
  "application/xml": "xml",
  "application/hl7-cda+xml": "xml",
  "image/tiff": "tif",
  "image/jpeg": "jpg",
  "image/png": "png",
};

// the filename-extension axis; kinds derive from this single map
const EXT_TO_KIND: Record<string, string> = {
  pdf: "pdf",
  doc: "doc",
  docx: "docx",
  xlsx: "xlsx",
  pptx: "pptx",
  rtf: "rtf",
  txt: "txt",
  md: "md",
  htm: "html",
  html: "html",
  xml: "xml",
  tif: "tif",
  tiff: "tif",
  jpg: "jpg",
  jpeg: "jpg",
  png: "png",
};
const SUPPORTED_KINDS = [...new Set(Object.values(EXT_TO_KIND))].join(", ");

function die(msg: string): never {
  console.error(JSON.stringify({ error: msg }));
  process.exit(1);
}

if (import.meta.main) {
  const args = process.argv.slice(2);
  const ctIdx = args.indexOf("--content-type");
  const contentType = ctIdx >= 0 ? args.splice(ctIdx, 2)[1] : undefined;
  const [input] = args;
  if (!input) die("usage: extract.ts <input-file> [--content-type <mime>]");

  const mimeKind = contentType
    ? KIND_BY_MIME[contentType.split(";")[0]!.trim().toLowerCase()]
    : undefined;
  const ext = input.match(/\.([a-z0-9]+)$/i)?.[1]?.toLowerCase();
  const kind = mimeKind ?? EXT_TO_KIND[ext ?? ""];
  if (!kind)
    die(
      `cannot determine format of ${input} — pass --content-type (supported: ${SUPPORTED_KINDS})`,
    );

  if (kind === "rtf") {
    console.log(JSON.stringify({ text: decodeRtf(readFileSync(input, "utf8")), method: "rtf" }));
  } else if (kind === "xml") {
    const text = decodeXml(readFileSync(input, "utf8"));
    if (text === null)
      die("XML embeds a base64 binary and has no text narrative — nothing extractable as text");
    console.log(JSON.stringify({ text, method: "xml" }));
  } else if (kind === "txt" || kind === "md" || kind === "html") {
    console.log(JSON.stringify({ text: readFileSync(input, "utf8"), method: "passthrough" }));
  } else {
    const lit = resolveLit();
    const r = extractWithMethod(lit, input, kind === "pdf");
    if (r == null)
      die(
        lit
          ? `extraction failed for ${input}`
          : `liteparse not found (run \`bun install\` in the doc-extract skill dir)${kind === "pdf" ? " and pdftotext fallback failed" : ` — required for .${kind}`}`,
      );
    const pages = r.text.match(/^=== \[page \d+\] ===$/gm)?.length;
    console.log(JSON.stringify({ text: r.text, method: r.method, ...(pages ? { pages } : {}) }));
  }
}
