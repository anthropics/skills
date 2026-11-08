// Text decoding for clinical document formats — the single copy shared by
// this skill's extract.ts and the fhir MCP server (servers/fhir/src/documents.mjs
// imports it directly). Dependency-free on purpose: the previous `rtf-to-text`
// npm dep was a day-old single-maintainer package at adoption — unacceptable
// supply-chain surface for clinical content.

// content is untrusted — an out-of-range reference must not throw
/** @param {number} n @returns {string} */
function codePoint(n) {
  return n >= 0 && n <= 0x10ffff ? String.fromCodePoint(n) : "�";
}

/** @type {Record<string, string>} */
const NAMED_ENTITIES = {
  nbsp: " ",
  quot: '"',
  apos: "'",
  lt: "<",
  gt: ">",
  amp: "&",
};

// single pass — matching &amp; as one entity also prevents double-decoding
/** @param {string} s @returns {string} */
function decodeEntities(s) {
  return s.replace(/&(?:#x([0-9a-f]+)|#(\d+)|(nbsp|quot|apos|lt|gt|amp));/gi, (_, hex, dec, name) =>
    hex
      ? codePoint(parseInt(hex, 16))
      : dec
        ? codePoint(parseInt(dec, 10))
        : NAMED_ENTITIES[String(name).toLowerCase()],
  );
}

/** @param {string} body @returns {string} */
export function stripMarkup(body) {
  return decodeEntities(
    body
      .replace(/<(script|style)[\s\S]*?<\/\1>/gi, "")
      .replace(/<!--[\s\S]*?-->/g, "")
      // one pass over the whitespace-bearing tags: cells → tab, blocks/breaks → newline
      .replace(
        /<\/(td|th)>|<br\s*\/?>|<\/(?:p|div|li|tr|h[1-6]|paragraph|item|caption|content|title|thead|tbody)>/gi,
        (_, cell) => (cell ? "\t" : "\n"),
      )
      .replace(/<[^>]+>/g, ""),
  )
    .replace(/[ \t]+\n/g, "\n")
    .replace(/\n{3,}/g, "\n\n");
}

// A single unbroken base64 run this long is an embedded binary (Cerner report
// XML base64s the whole PDF; CDA does the same in nonXMLBody), never prose.
// Linear scan, not a regex — the backtracking engine re-tests per position,
// which adversarial near-threshold runs make quadratic on untrusted input.
/** @param {string} s @param {number} [min] @returns {boolean} */
export function hasEmbeddedBase64(s, min = 10_000) {
  let run = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    const isB64 =
      (c >= 48 && c <= 57) ||
      (c >= 65 && c <= 90) ||
      (c >= 97 && c <= 122) ||
      c === 43 ||
      c === 47 ||
      c === 61;
    run = isB64 ? run + 1 : 0;
    if (run >= min) return true;
  }
  return false;
}

// C-CDA (and CDA R2) documents carry the human-readable note in <title> and
// narrative <text> blocks; the machine-readable <entry> content is noise for
// note reading. A flat scan over title/text elements (document order) rather
// than section matching — CDA allows nested sections, which a lazy
// <section>…</section> match would truncate. Narrative parts that are
// themselves embedded base64 (nonXMLBody's <text>, observationMedia) are
// dropped; if nothing readable remains — or a non-CDA XML's payload is an
// embedded binary (vendor report formats that base64 the document) — the
// document is not decodable as text (null).
/** @param {string} body @returns {string | null} */
export function decodeXml(body) {
  // CDA's nonXMLBody replaces the structured narrative entirely — no text here
  if (/<nonXMLBody[\s>]/.test(body)) return null;
  if (/<ClinicalDocument[\s>]/.test(body)) {
    /** @type {string[]} */
    const parts = [];
    for (const m of body.matchAll(/<(title|text)[\s>][\s\S]*?<\/\1>/g)) {
      const el = m[0].slice(m[0].indexOf(">") + 1, m[0].lastIndexOf("<"));
      if (hasEmbeddedBase64(el)) continue;
      const cleaned = stripMarkup(el).trim();
      if (cleaned) parts.push(m[1] === "title" ? `## ${cleaned}` : cleaned);
    }
    return parts.length > 0 ? parts.join("\n\n") : null;
  }
  if (hasEmbeddedBase64(body)) return null;
  return stripMarkup(body);
}

// Destination groups whose content is formatting/metadata, never note text.
// All `{\*` groups are optional destinations — safe to drop wholesale.
const RTF_SKIP_DESTS =
  /^(fonttbl|colortbl|stylesheet|info|pict|object|themedata|listtable|listoverridetable|latentstyles|datastore|filetbl|revtbl|xmlnstbl|header|footer)/;

const RTF_NEWLINE_WORDS = new Set(["par", "line", "row", "sect", "page"]);

// cp1252's 0x80–0x9F block (curly quotes, dashes, bullet) — RTF's default
// codepage, where \'93 etc. differ from latin-1 control chars.
/** @type {Record<number, number>} */
// prettier-ignore
const CP1252_HIGH = {
  0x80: 0x20ac, 0x82: 0x201a, 0x83: 0x0192, 0x84: 0x201e, 0x85: 0x2026,
  0x86: 0x2020, 0x87: 0x2021, 0x88: 0x02c6, 0x89: 0x2030, 0x8a: 0x0160,
  0x8b: 0x2039, 0x8c: 0x0152, 0x8e: 0x017d, 0x91: 0x2018, 0x92: 0x2019,
  0x93: 0x201c, 0x94: 0x201d, 0x95: 0x2022, 0x96: 0x2013, 0x97: 0x2014,
  0x98: 0x02dc, 0x99: 0x2122, 0x9a: 0x0161, 0x9b: 0x203a, 0x9c: 0x0153,
  0x9e: 0x017e, 0x9f: 0x0178,
};

// sticky (\y) so it runs at an offset without slicing the body — V8 flattens
// (copies) sliced strings for regex, which would make the scan quadratic
const RTF_WORD = /\\([a-z]+)(-?\d+)? ?/y;

// index of the next structural char at or after `from`, or body.length
/** @param {string} body @param {number} from @returns {number} */
function nextStructural(body, from) {
  for (let j = from; j < body.length; j++) {
    const c = body[j];
    if (c === "{" || c === "}" || c === "\\") return j;
  }
  return body.length;
}

// Minimal RTF-to-text: tracks group nesting, drops non-content destination
// groups, maps the paragraph/tab control words to whitespace, and decodes
// \'xx / \uN escapes. Not a full RTF parser — good enough for EHR note bodies.
/** @param {string} body @returns {string} */
export function decodeRtf(body) {
  let out = "";
  let i = 0;
  let skipDepth = 0; // >0 while inside a dropped destination group
  let depth = 0;
  let ucSkip = 1; // \ucN: fallback chars to swallow after \uN
  while (i < body.length) {
    const c = body[i];
    if (c === "{") {
      depth++;
      if (skipDepth === 0) {
        const peek = body.slice(i + 1, i + 24);
        if (peek.startsWith("\\*") || RTF_SKIP_DESTS.test(/^\\([a-z]+)/.exec(peek)?.[1] ?? "")) {
          skipDepth = depth;
        }
      }
      i++;
      continue;
    }
    if (c === "}") {
      if (skipDepth === depth) skipDepth = 0;
      if (depth > 0) depth--;
      i++;
      continue;
    }
    if (c === "\\") {
      const esc = body[i + 1];
      if (esc === "\\" || esc === "{" || esc === "}") {
        if (skipDepth === 0) out += esc;
        i += 2;
        continue;
      }
      if (esc === "'") {
        const hex = body.slice(i + 2, i + 4);
        if (/^[0-9a-f]{2}$/i.test(hex)) {
          if (skipDepth === 0) {
            const code = parseInt(hex, 16);
            out += String.fromCharCode(CP1252_HIGH[code] ?? code);
          }
          i += 4;
        } else {
          i += 2; // malformed escape — don't swallow following text
        }
        continue;
      }
      if (esc === "~") {
        if (skipDepth === 0) out += " ";
        i += 2;
        continue;
      }
      RTF_WORD.lastIndex = i;
      const word = RTF_WORD.exec(body);
      if (word) {
        const [matched, name, arg] = word;
        i += matched.length;
        if (name === "bin" && arg) {
          // \binN's payload is N raw BYTES; after utf-8 decoding the char
          // count can be smaller, so this may overshoot — the skipDepth ===
          // depth reset self-heals at the next real `}` at the cost of the
          // text in between
          i = Math.min(body.length, i + Math.max(0, parseInt(arg, 10)));
        } else if (name === "uc" && arg) {
          ucSkip = Math.max(0, parseInt(arg, 10));
        } else if (skipDepth === 0) {
          if (RTF_NEWLINE_WORDS.has(name)) out += "\n";
          else if (name === "tab" || name === "cell") out += "\t";
          else if (name === "u" && arg) {
            const cp = parseInt(arg, 10);
            out += String.fromCharCode(cp < 0 ? cp + 65536 : cp);
            // swallow the ucSkip fallback chars that follow \uN (plain or \'xx)
            for (let n = 0; n < ucSkip; n++) {
              if (/^\\'[0-9a-f]{2}/i.test(body.slice(i, i + 4))) i += 4;
              else if (body[i] && !"\\{}".includes(body[i])) i++;
              else break;
            }
          }
        }
        continue;
      }
      i += 2; // unknown escape (\<symbol>)
      continue;
    }
    if (skipDepth > 0) {
      // bulk-skip dropped groups (pict hex runs are megabytes): jump to the
      // next structural char instead of stepping per character
      i = Math.max(i + 1, nextStructural(body, i));
      continue;
    }
    // plain-text run — append the whole slice at once, not char-by-char
    const end = Math.max(i + 1, nextStructural(body, i));
    out += body.slice(i, end).replace(/[\r\n]/g, "");
    i = end;
  }
  return out
    .replace(/[ \t]+\n/g, "\n")
    .replace(/\n{3,}/g, "\n\n")
    .trim();
}
