export interface YouTubeTranscriptSegment {
  start: number;
  end: number;
  text: string;
}

export interface YouTubeChapter {
  title: string;
  time: number;
}

interface RenderYouTubeTranscriptMarkdownInput {
  description?: string;
  segments: YouTubeTranscriptSegment[];
  chapters: YouTubeChapter[];
}

const DESCRIPTION_CHAPTER_RE = /^((?:\d{1,2}:)?\d{1,2}:\d{2})(?:\s+[-|:]\s+|\s+)(.+)$/;
const YOUTUBE_THUMBNAIL_VARIANTS = [
  "maxresdefault.jpg",
  "sddefault.jpg",
  "hqdefault.jpg",
  "mqdefault.jpg",
  "default.jpg",
];

export function isYouTubeHost(hostname: string): boolean {
  return [
    "youtube.com",
    "www.youtube.com",
    "m.youtube.com",
    "youtu.be",
  ].includes(hostname);
}

export function parseYouTubeVideoId(url: URL): string | null {
  if (url.hostname === "youtu.be") {
    return url.pathname.split("/").filter(Boolean)[0] ?? null;
  }

  if (url.pathname === "/watch") {
    return url.searchParams.get("v");
  }

  const shortsMatch = url.pathname.match(/^\/shorts\/([^/?#]+)/);
  if (shortsMatch) {
    return shortsMatch[1];
  }

  const liveMatch = url.pathname.match(/^\/live\/([^/?#]+)/);
  if (liveMatch) {
    return liveMatch[1];
  }

  return null;
}

function parseTimestampValue(raw: string): number | null {
  const parts = raw
    .split(":")
    .map((part) => Number.parseInt(part, 10))
    .filter((part) => Number.isFinite(part));

  if (parts.length < 2 || parts.length > 3) {
    return null;
  }

  if (parts.some((part) => part < 0)) {
    return null;
  }

  if (parts.length === 2) {
    const [minutes, seconds] = parts;
    return minutes * 60 + seconds;
  }

  const [hours, minutes, seconds] = parts;
  return hours * 3600 + minutes * 60 + seconds;
}

export function formatTimestamp(totalSeconds: number): string {
  const rounded = Math.max(0, Math.floor(totalSeconds));
  const hours = Math.floor(rounded / 3600);
  const minutes = Math.floor((rounded % 3600) / 60);
  const seconds = rounded % 60;

  if (hours > 0) {
    return `${hours}:${String(minutes).padStart(2, "0")}:${String(seconds).padStart(2, "0")}`;
  }
  return `${minutes}:${String(seconds).padStart(2, "0")}`;
}

export function formatTimestampRange(start: number, end: number): string {
  const safeStart = Math.max(0, start);
  const safeEnd = Math.max(safeStart, end);
  return `[${formatTimestamp(safeStart)} -> ${formatTimestamp(safeEnd)}]`;
}

export function normalizeYouTubeChapters(chapters: YouTubeChapter[]): YouTubeChapter[] {
  const seenTimes = new Set<number>();

  return chapters
    .map((chapter) => ({
      title: chapter.title.trim(),
      time: Math.max(0, Math.floor(chapter.time)),
    }))
    .filter((chapter) => chapter.title)
    .sort((left, right) => left.time - right.time)
    .filter((chapter) => {
      if (seenTimes.has(chapter.time)) {
        return false;
      }
      seenTimes.add(chapter.time);
      return true;
    });
}

export function parseYouTubeDescriptionChapters(description?: string | null): YouTubeChapter[] {
  if (!description) {
    return [];
  }

  const chapters: YouTubeChapter[] = [];
  const seen = new Set<string>();

  for (const rawLine of description.replace(/\r\n/g, "\n").split("\n")) {
    const line = rawLine.trim();
    if (!line) {
      continue;
    }

    const match = line.match(DESCRIPTION_CHAPTER_RE);
    if (!match) {
      continue;
    }

    const time = parseTimestampValue(match[1]);
    const title = match[2]?.trim();
    if (time === null || !title) {
      continue;
    }

    const key = `${time}:${title.toLowerCase()}`;
    if (seen.has(key)) {
      continue;
    }

    seen.add(key);
    chapters.push({ title, time });
  }

  const normalized = normalizeYouTubeChapters(chapters);
  if (normalized.length >= 2) {
    return normalized;
  }

  if (normalized.length === 1 && normalized[0]?.time === 0) {
    return normalized;
  }

  return [];
}

function renderDescriptionMarkdown(description: string): string {
  return description
    .replace(/\r\n/g, "\n")
    .trim()
    .split(/\n{2,}/)
    .map((block) => block.split("\n").map((line) => line.trimEnd()).join("  \n"))
    .join("\n\n")
    .trim();
}

function renderSegmentLine(segment: YouTubeTranscriptSegment): string {
  return `${formatTimestampRange(segment.start, segment.end)} ${segment.text}`;
}

export function renderYouTubeTranscriptMarkdown({
  description,
  segments,
  chapters,
}: RenderYouTubeTranscriptMarkdownInput): string {
  if (segments.length === 0) {
    return "";
  }

  const parts: string[] = [];
  const normalizedDescription = description?.trim();
  const transcriptEnd = segments.reduce((maxEnd, segment) => Math.max(maxEnd, segment.end, segment.start), 0);
  const normalizedChapters = normalizeYouTubeChapters(chapters).filter(
    (chapter) => transcriptEnd <= 0 || chapter.time < transcriptEnd,
  );

  if (normalizedDescription) {
    parts.push("## Description");
    parts.push(renderDescriptionMarkdown(normalizedDescription));
  }

  if (normalizedChapters.length > 0) {
    parts.push("## Chapters");

    for (let index = 0; index < normalizedChapters.length; index += 1) {
      const chapter = normalizedChapters[index];
      const nextChapter = normalizedChapters[index + 1];
      const chapterEnd = nextChapter ? nextChapter.time : transcriptEnd;
      const chapterSegments = segments.filter(
        (segment) => segment.start >= chapter.time && segment.start < chapterEnd,
      );

      parts.push(`### ${chapter.title} ${formatTimestampRange(chapter.time, chapterEnd)}`);

      if (chapterSegments.length > 0) {
        parts.push(chapterSegments.map(renderSegmentLine).join("\n"));
      }
    }
  } else {
    parts.push("## Transcript");
    parts.push(segments.map(renderSegmentLine).join("\n"));
  }

  return parts.filter(Boolean).join("\n\n").trim();
}

function normalizeThumbnailKey(url: string): string {
  try {
    const parsed = new URL(url);
    return `${parsed.origin}${parsed.pathname}`;
  } catch {
    return url;
  }
}

export function buildYouTubeThumbnailCandidates(videoId: string, listedUrls: string[]): string[] {
  const candidates = [
    ...YOUTUBE_THUMBNAIL_VARIANTS.map((variant) => `https://i.ytimg.com/vi/${videoId}/${variant}`),
    ...listedUrls,
  ];

  const seen = new Set<string>();
  return candidates.filter((candidate) => {
    if (!candidate) {
      return false;
    }

    const key = normalizeThumbnailKey(candidate);
    if (seen.has(key)) {
      return false;
    }

    seen.add(key);
    return true;
  });
}
