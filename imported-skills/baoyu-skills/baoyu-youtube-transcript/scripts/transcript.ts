import { htmlUnescape, makeError, stripTags } from "./shared.ts";
import type { Sentence, Snippet, TranscriptInfo, VideoMeta } from "./types.ts";

interface Paragraph {
  text: string;
  start: number;
  end: number;
}

const SENTENCE_END_RE = /[.?!…。？！⁈⁇‼‽．]/;

export function parseTranscriptXml(xml: string): Snippet[] {
  const snippets: Snippet[] = [];
  const pattern = /<text\s+start="([^"]*)"(?:\s+dur="([^"]*)")?[^>]*>([\s\S]*?)<\/text>/g;
  let match: RegExpExecArray | null;
  while ((match = pattern.exec(xml)) !== null) {
    const raw = match[3];
    if (!raw) continue;
    snippets.push({
      text: htmlUnescape(stripTags(raw)),
      start: parseFloat(match[1]),
      duration: parseFloat(match[2] || "0"),
    });
  }
  return snippets;
}

export function parseTranscriptJson3(text: string): Snippet[] {
  const data = JSON.parse(text);
  const events = Array.isArray(data?.events) ? data.events : [];
  const snippets: Snippet[] = [];
  for (const event of events) {
    const segs = Array.isArray(event?.segs) ? event.segs : [];
    const textParts = segs
      .map((seg: any) => htmlUnescape(String(seg?.utf8 || "").replace(/\n+/g, " ").trim()))
      .filter(Boolean);
    const merged = mergeTexts(textParts).trim();
    if (!merged) continue;
    snippets.push({
      text: merged,
      start: Number(event?.tStartMs || 0) / 1000,
      duration: Number(event?.dDurationMs || 0) / 1000,
    });
  }
  return snippets;
}

function parseSrt(srt: string): Snippet[] {
  const blocks = srt.trim().split(/\n\n+/);
  const snippets: Snippet[] = [];
  for (const block of blocks) {
    const lines = block.split("\n");
    if (lines.length < 3) continue;
    const match = lines[1].match(/(\d{2}):(\d{2}):(\d{2}),(\d{3})\s*-->\s*(\d{2}):(\d{2}):(\d{2}),(\d{3})/);
    if (!match) continue;
    const start = parseInt(match[1]) * 3600 + parseInt(match[2]) * 60 + parseInt(match[3]) + parseInt(match[4]) / 1000;
    const end = parseInt(match[5]) * 3600 + parseInt(match[6]) * 60 + parseInt(match[7]) + parseInt(match[8]) / 1000;
    snippets.push({ text: lines.slice(2).join(" "), start, duration: end - start });
  }
  return snippets;
}

export function parseWebVtt(vtt: string): Snippet[] {
  const blocks = vtt
    .replace(/^WEBVTT\s*/m, "")
    .trim()
    .split(/\n\n+/);
  const snippets: Snippet[] = [];
  for (const block of blocks) {
    const lines = block.split("\n").map((line) => line.trim()).filter(Boolean);
    const tsLine = lines.find((line) => line.includes("-->"));
    if (!tsLine) continue;
    const match = tsLine.match(
      /(?:(\d{2}):)?(\d{2}):(\d{2})\.(\d{3})\s*-->\s*(?:(\d{2}):)?(\d{2}):(\d{2})\.(\d{3})/
    );
    if (!match) continue;
    const start =
      (match[1] ? parseInt(match[1]) : 0) * 3600 +
      parseInt(match[2]) * 60 +
      parseInt(match[3]) +
      parseInt(match[4]) / 1000;
    const end =
      (match[5] ? parseInt(match[5]) : 0) * 3600 +
      parseInt(match[6]) * 60 +
      parseInt(match[7]) +
      parseInt(match[8]) / 1000;
    const text = htmlUnescape(stripTags(lines.slice(lines.indexOf(tsLine) + 1).join(" ").replace(/\s+/g, " ").trim()));
    if (!text) continue;
    snippets.push({ text, start, duration: end - start });
  }
  return snippets;
}

export function parseTranscriptPayload(payload: string, url: string): Snippet[] {
  const normalized = payload.trimStart();
  if (url.includes("fmt=json3") || normalized.startsWith("{")) return parseTranscriptJson3(payload);
  if (normalized.startsWith("WEBVTT")) return parseWebVtt(payload);
  if (/^\d+\s*\n\d{2}:\d{2}:\d{2},\d{3}\s*-->/.test(normalized)) return parseSrt(payload);
  return parseTranscriptXml(payload);
}

function isCJK(ch: string): boolean {
  const code = ch.charCodeAt(0);
  return (code >= 0x4E00 && code <= 0x9FFF) ||
    (code >= 0x3040 && code <= 0x309F) ||
    (code >= 0x30A0 && code <= 0x30FF) ||
    (code >= 0xAC00 && code <= 0xD7AF) ||
    (code >= 0x3400 && code <= 0x4DBF) ||
    (code >= 0xF900 && code <= 0xFAFF);
}

function splitSnippetAtPunctuation(snippet: Snippet): { text: string; start: number; end: number }[] {
  const { text, start, duration } = snippet;
  const end = start + duration;
  if (!text.length) return [];

  const splitPoints: number[] = [];
  for (let i = 0; i < text.length; i++) {
    if (SENTENCE_END_RE.test(text[i])) {
      while (i + 1 < text.length && SENTENCE_END_RE.test(text[i + 1])) i++;
      if (i < text.length - 1) splitPoints.push(i);
    }
  }

  if (!splitPoints.length) return [{ text, start, end }];

  const parts: { text: string; start: number; end: number }[] = [];
  let prev = 0;
  for (const pos of splitPoints) {
    const partText = text.slice(prev, pos + 1).trim();
    if (partText) {
      parts.push({
        text: partText,
        start: start + (prev / text.length) * duration,
        end: start + ((pos + 1) / text.length) * duration,
      });
    }
    prev = pos + 1;
  }

  const remaining = text.slice(prev).trim();
  if (remaining) parts.push({ text: remaining, start: start + (prev / text.length) * duration, end });

  return parts;
}

function mergeTexts(texts: string[]): string {
  if (!texts.length) return "";
  let result = texts[0];
  for (let i = 1; i < texts.length; i++) {
    const next = texts[i];
    if (!next) continue;
    const lastChar = result[result.length - 1];
    const firstChar = next[0];
    if (isCJK(lastChar) || isCJK(firstChar)) {
      result += next;
    } else {
      result = result.trimEnd() + " " + next.trimStart();
    }
  }
  return result.replace(/ {2,}/g, " ");
}

export function ts(time: number): string {
  const h = Math.floor(time / 3600);
  const m = Math.floor((time % 3600) / 60);
  const s = Math.floor(time % 60);
  return `${String(h).padStart(2, "0")}:${String(m).padStart(2, "0")}:${String(s).padStart(2, "0")}`;
}

function tsMs(time: number, sep: string): string {
  const h = Math.floor(time / 3600);
  const m = Math.floor((time % 3600) / 60);
  const s = Math.floor(time % 60);
  const ms = Math.round((time - Math.floor(time)) * 1000);
  return `${String(h).padStart(2, "0")}:${String(m).padStart(2, "0")}:${String(s).padStart(2, "0")}${sep}${String(ms).padStart(3, "0")}`;
}

function parseTs(time: string): number {
  const [h, m, s] = time.split(":").map(Number);
  return h * 3600 + m * 60 + s;
}

export function segmentIntoSentences(snippets: Snippet[]): Sentence[] {
  const parts: { text: string; start: number; end: number }[] = [];
  for (const snippet of snippets) parts.push(...splitSnippetAtPunctuation(snippet));

  const sentences: Sentence[] = [];
  let buffer: { text: string; start: number; end: number }[] = [];

  for (const part of parts) {
    buffer.push(part);
    if (SENTENCE_END_RE.test(part.text[part.text.length - 1])) {
      sentences.push({
        text: mergeTexts(buffer.map((entry) => entry.text)),
        start: ts(buffer[0].start),
        end: ts(buffer[buffer.length - 1].end),
      });
      buffer = [];
    }
  }

  if (buffer.length) {
    sentences.push({
      text: mergeTexts(buffer.map((entry) => entry.text)),
      start: ts(buffer[0].start),
      end: ts(buffer[buffer.length - 1].end),
    });
  }

  return sentences;
}

function groupSentenceParas(sentences: Sentence[]): Paragraph[] {
  if (!sentences.length) return [];
  const paragraphs: Paragraph[] = [];
  let buffer: Sentence[] = [];
  for (let i = 0; i < sentences.length; i++) {
    buffer.push(sentences[i]);
    const last = i === sentences.length - 1;
    const gap = !last && parseTs(sentences[i + 1].start) - parseTs(sentences[i].end) > 2;
    if (last || gap || buffer.length >= 5) {
      paragraphs.push({
        text: mergeTexts(buffer.map((sentence) => sentence.text)),
        start: parseTs(buffer[0].start),
        end: parseTs(buffer[buffer.length - 1].end),
      });
      buffer = [];
    }
  }
  return paragraphs;
}

export function formatSrt(snippets: Snippet[]): string {
  return snippets
    .map((snippet, index) => {
      const end = index < snippets.length - 1 && snippets[index + 1].start < snippet.start + snippet.duration
        ? snippets[index + 1].start
        : snippet.start + snippet.duration;
      return `${index + 1}\n${tsMs(snippet.start, ",")} --> ${tsMs(end, ",")}\n${snippet.text}`;
    })
    .join("\n\n") + "\n";
}

function yamlEscape(value: string): string {
  if (/[:"'{}\[\]#&*!|>%@`\n]/.test(value) || value.trim() !== value) {
    return `"${value.replace(/\\/g, "\\\\").replace(/"/g, '\\"')}"`;
  }
  return value;
}

function extractSummary(description: string): string {
  if (!description) return "";
  const firstPara = description.split(/\n\s*\n/)[0].trim();
  const lines = firstPara.split("\n").filter((line) => !/^\s*(https?:\/\/|#|@|\d+:\d+)/.test(line) && line.trim());
  return lines.join(" ").slice(0, 300).trim();
}

export function formatMarkdown(
  sentences: Sentence[],
  meta: VideoMeta,
  opts: { timestamps: boolean; chapters: boolean; speakers: boolean },
  snippets?: Snippet[]
): string {
  const summary = extractSummary(meta.description);
  let md = "---\n";
  md += `title: ${yamlEscape(meta.title)}\n`;
  md += `channel: ${yamlEscape(meta.channel)}\n`;
  if (meta.publishDate) md += `date: ${meta.publishDate}\n`;
  md += `url: ${yamlEscape(meta.url)}\n`;
  if (meta.coverImage) md += `cover: ${meta.coverImage}\n`;
  if (summary) md += `description: ${yamlEscape(summary)}\n`;
  if (meta.language) md += `language: ${meta.language.code}\n`;
  md += "---\n\n";

  if (opts.speakers) {
    md += `# ${meta.title}\n\n`;
    if (summary) md += `${summary}\n\n`;
    if (meta.description) md += `# Description\n\n${meta.description.trim()}\n\n`;
    if (meta.chapters.length) {
      md += "# Chapters\n\n";
      for (const chapter of meta.chapters) md += `* [${ts(chapter.start)}] ${chapter.title}\n`;
      md += "\n";
    }
    md += "# Transcript\n\n";
    md += snippets ? formatSrt(snippets) : "";
    return md;
  }

  md += `# ${meta.title}\n\n`;
  if (summary) md += `${summary}\n\n`;

  const chapters = opts.chapters ? meta.chapters : [];
  if (chapters.length) {
    md += "## Table of Contents\n\n";
    for (const chapter of chapters) md += opts.timestamps ? `* [${ts(chapter.start)}] ${chapter.title}\n` : `* ${chapter.title}\n`;
    md += "\n";
    if (meta.coverImage) md += `\n![cover](${meta.coverImage})\n`;
    md += "\n";
    for (let i = 0; i < chapters.length; i++) {
      const nextStart = i < chapters.length - 1 ? chapters[i + 1].start : Infinity;
      const chapterSentences = sentences.filter((sentence) => parseTs(sentence.start) >= chapters[i].start && parseTs(sentence.start) < nextStart);
      const paragraphs = groupSentenceParas(chapterSentences);
      md += opts.timestamps ? `## [${ts(chapters[i].start)}] ${chapters[i].title}\n\n` : `## ${chapters[i].title}\n\n`;
      for (const paragraph of paragraphs) {
        md += opts.timestamps ? `${paragraph.text} [${ts(paragraph.start)} → ${ts(paragraph.end)}]\n\n` : `${paragraph.text}\n\n`;
      }
      md += "\n";
    }
  } else {
    const paragraphs = groupSentenceParas(sentences);
    for (const paragraph of paragraphs) {
      md += opts.timestamps ? `${paragraph.text} [${ts(paragraph.start)} → ${ts(paragraph.end)}]\n\n` : `${paragraph.text}\n\n`;
    }
  }

  return md.trimEnd() + "\n";
}

export function formatListOutput(videoId: string, title: string, transcripts: TranscriptInfo[]): string {
  const manual = transcripts.filter((transcript) => !transcript.isGenerated);
  const generated = transcripts.filter((transcript) => transcript.isGenerated);
  const translationLanguages = transcripts.find((transcript) => transcript.translationLanguages.length > 0)?.translationLanguages || [];
  const formatList = (list: TranscriptInfo[]) =>
    list.length
      ? list.map((transcript) => ` - ${transcript.languageCode} ("${transcript.language}")${transcript.isTranslatable ? " [TRANSLATABLE]" : ""}`).join("\n")
      : "None";
  const formatTranslations = translationLanguages.length
    ? translationLanguages.map((language) => ` - ${language.languageCode} ("${language.language}")`).join("\n")
    : "None";
  return `Transcripts for ${videoId}${title ? ` (${title})` : ""}:\n\n(MANUALLY CREATED)\n${formatList(manual)}\n\n(GENERATED)\n${formatList(generated)}\n\n(TRANSLATION LANGUAGES)\n${formatTranslations}`;
}

export function findTranscript(
  transcripts: TranscriptInfo[],
  languages: string[],
  excludeGenerated: boolean,
  excludeManual: boolean
): TranscriptInfo {
  let filtered = transcripts;
  if (excludeGenerated) filtered = filtered.filter((transcript) => !transcript.isGenerated);
  if (excludeManual) filtered = filtered.filter((transcript) => transcript.isGenerated);
  for (const language of languages) {
    const found = filtered.find((transcript) => transcript.languageCode === language);
    if (found) return found;
  }
  const available = filtered.map((transcript) => `${transcript.languageCode} ("${transcript.language}")`).join(", ");
  throw makeError(`No transcript found for languages [${languages.join(", ")}]. Available: ${available || "none"}`, "NO_TRANSCRIPT");
}
