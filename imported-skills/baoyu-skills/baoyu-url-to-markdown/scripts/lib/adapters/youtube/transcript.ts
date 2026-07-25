import type { ExtractedDocument } from "../../extract/document";
import { detectInteractionGate } from "../../browser/interaction-gates";
import {
  buildYouTubeThumbnailCandidates,
  parseYouTubeDescriptionChapters,
  renderYouTubeTranscriptMarkdown,
  type YouTubeChapter,
  type YouTubeTranscriptSegment,
} from "./utils";

interface CaptionInfo {
  captionUrl: string;
  language: string;
  kind: string;
  available: string[];
  title?: string;
  author?: string;
  authorUrl?: string;
  channelId?: string;
  description?: string;
  publishedAt?: string;
  viewCount?: number;
  durationSeconds?: number;
  keywords: string[];
  category?: string;
  isLiveContent?: boolean;
  coverImages: string[];
}

function normalizeUrl(url: string | undefined): string | undefined {
  if (!url) {
    return undefined;
  }

  try {
    const parsed = new URL(url);
    if (parsed.protocol === "http:") {
      parsed.protocol = "https:";
    }
    return parsed.toString();
  } catch {
    return url;
  }
}

function buildSummary(description: string | undefined, segments: YouTubeTranscriptSegment[]): string | undefined {
  const descriptionSummary = description
    ?.replace(/\r\n/g, "\n")
    .split("\n")
    .map((line) => line.trim())
    .find((line) => line && !/^https?:\/\//i.test(line));

  if (descriptionSummary) {
    return descriptionSummary.slice(0, 240);
  }

  const transcriptSummary = segments
    .slice(0, 8)
    .map((segment) => segment.text)
    .join(" ")
    .slice(0, 240)
    .trim();

  return transcriptSummary || undefined;
}

async function canFetchThumbnail(url: string): Promise<boolean> {
  try {
    const response = await fetch(url, { method: "HEAD", redirect: "follow" });
    if (response.ok) {
      return true;
    }

    if (response.status === 405) {
      const fallbackResponse = await fetch(url, {
        method: "GET",
        headers: { Range: "bytes=0-0" },
        redirect: "follow",
      });
      return fallbackResponse.ok;
    }
  } catch {
    return false;
  }

  return false;
}

async function resolveBestCoverImage(videoId: string, coverImages: string[]): Promise<string | undefined> {
  const candidates = buildYouTubeThumbnailCandidates(videoId, coverImages);

  for (const candidate of candidates) {
    if (await canFetchThumbnail(candidate)) {
      return candidate;
    }
  }

  return candidates[0];
}

export async function extractYouTubeTranscriptDocument(
  context: Parameters<import("../types").Adapter["process"]>[0],
  videoId: string,
): Promise<ExtractedDocument | null> {
  const videoUrl = `https://www.youtube.com/watch?v=${videoId}`;
  await context.browser.goto(videoUrl, context.timeoutMs);

  const interaction = await detectInteractionGate(context.browser);
  if (interaction) {
    context.log.debug(`Interaction gate detected on YouTube: ${interaction.provider}`);
    return null;
  }

  try {
    await context.network.waitForIdle({
      idleMs: 1_000,
      timeoutMs: Math.min(context.timeoutMs, 8_000),
    });
  } catch {
    context.log.debug("Network idle timed out on YouTube load.");
  }

  const captionInfo = await context.browser.evaluate<CaptionInfo | { error: string }>(`
    (async () => {
      function readText(value) {
        if (!value) return undefined;
        if (typeof value === 'string') {
          const text = value.trim();
          return text || undefined;
        }
        if (typeof value.simpleText === 'string') {
          const text = value.simpleText.trim();
          return text || undefined;
        }
        if (Array.isArray(value.runs)) {
          const text = value.runs
            .map((run) => typeof run?.text === 'string' ? run.text : '')
            .join('')
            .trim();
          return text || undefined;
        }
        return undefined;
      }

      function parsePositiveInteger(value) {
        if (typeof value === 'number' && Number.isFinite(value) && value >= 0) {
          return Math.floor(value);
        }
        if (typeof value !== 'string') {
          return undefined;
        }
        const normalized = value.replace(/[^\\d]/g, '');
        if (!normalized) {
          return undefined;
        }
        const parsed = Number.parseInt(normalized, 10);
        return Number.isFinite(parsed) ? parsed : undefined;
      }

      const apiKey = window.ytcfg?.data_?.INNERTUBE_API_KEY;
      const playerResponse = window.ytInitialPlayerResponse;
      const videoDetails = playerResponse?.videoDetails || {};
      const microformat = playerResponse?.microformat?.playerMicroformatRenderer || {};
      const title =
        videoDetails.title ||
        readText(microformat.title) ||
        document.title.replace(/ - YouTube$/, '').trim();
      const author =
        videoDetails.author ||
        microformat.ownerChannelName ||
        document.querySelector('link[itemprop="name"]')?.getAttribute('content') ||
        undefined;
      const authorUrl =
        microformat.ownerProfileUrl ||
        (typeof videoDetails.channelId === 'string' && videoDetails.channelId
          ? 'https://www.youtube.com/channel/' + videoDetails.channelId
          : undefined);
      const description =
        readText(microformat.description) ||
        (typeof videoDetails.shortDescription === 'string' ? videoDetails.shortDescription.trim() : undefined);
      const keywords = Array.isArray(videoDetails.keywords)
        ? videoDetails.keywords.filter((keyword) => typeof keyword === 'string' && keyword.trim())
        : [];
      const thumbnails = [
        ...(Array.isArray(videoDetails.thumbnail?.thumbnails) ? videoDetails.thumbnail.thumbnails : []),
        ...(Array.isArray(microformat.thumbnail?.thumbnails) ? microformat.thumbnail.thumbnails : []),
      ]
        .filter((thumbnail) => typeof thumbnail?.url === 'string' && thumbnail.url)
        .sort((left, right) => ((right?.width || 0) * (right?.height || 0)) - ((left?.width || 0) * (left?.height || 0)))
        .map((thumbnail) => thumbnail.url);

      if (!apiKey) {
        return { error: 'INNERTUBE_API_KEY not found on page' };
      }

      const response = await fetch('/youtubei/v1/player?key=' + apiKey + '&prettyPrint=false', {
        method: 'POST',
        credentials: 'include',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          context: { client: { clientName: 'ANDROID', clientVersion: '20.10.38' } },
          videoId: ${JSON.stringify(videoId)}
        })
      });

      if (!response.ok) {
        return { error: 'InnerTube player API returned HTTP ' + response.status };
      }

      const data = await response.json();
      const renderer = data.captions?.playerCaptionsTracklistRenderer;
      if (!renderer?.captionTracks?.length) {
        return { error: 'No captions available for this video' };
      }

      const tracks = renderer.captionTracks;
      const track = tracks.find((item) => item.kind !== 'asr') || tracks[0];

      return {
        captionUrl: track.baseUrl,
        language: track.languageCode,
        kind: track.kind || 'manual',
        available: tracks.map((item) => {
          const languageLabel = readText(item.name) || item.languageCode;
          return item.kind === 'asr'
            ? languageLabel + ' [' + item.languageCode + ', auto]'
            : languageLabel + ' [' + item.languageCode + ']';
        }),
        title,
        author,
        authorUrl,
        channelId: typeof videoDetails.channelId === 'string' ? videoDetails.channelId : undefined,
        description,
        publishedAt:
          (typeof microformat.publishDate === 'string' && microformat.publishDate) ||
          (typeof microformat.uploadDate === 'string' && microformat.uploadDate) ||
          document.querySelector('meta[itemprop="datePublished"]')?.getAttribute('content') ||
          undefined,
        viewCount: parsePositiveInteger(videoDetails.viewCount) ?? parsePositiveInteger(microformat.viewCount),
        durationSeconds: parsePositiveInteger(videoDetails.lengthSeconds),
        keywords,
        category: typeof microformat.category === 'string' ? microformat.category : undefined,
        isLiveContent: Boolean(videoDetails.isLiveContent || microformat.isLiveContent),
        coverImages: thumbnails,
      };
    })()
  `);

  if ("error" in captionInfo) {
    context.log.debug(`YouTube transcript unavailable: ${captionInfo.error}`);
    return null;
  }

  const segments = await context.browser.evaluate<YouTubeTranscriptSegment[] | { error: string }>(`
    (async () => {
      const response = await fetch(${JSON.stringify(captionInfo.captionUrl)});
      const xml = await response.text();
      if (!xml) {
        return { error: 'Caption XML is empty' };
      }

      function getAttr(tag, name) {
        const needle = name + '="';
        const index = tag.indexOf(needle);
        if (index === -1) return '';
        const valueStart = index + needle.length;
        const valueEnd = tag.indexOf('"', valueStart);
        if (valueEnd === -1) return '';
        return tag.substring(valueStart, valueEnd);
      }

      function decodeEntities(value) {
        return value
          .replaceAll('&amp;', '&')
          .replaceAll('&lt;', '<')
          .replaceAll('&gt;', '>')
          .replaceAll('&quot;', '"')
          .replaceAll('&#39;', "'");
      }

      const marker = xml.includes('<p t="') ? '<p ' : '<text ';
      const endMarker = marker === '<p ' ? '</p>' : '</text>';
      const results = [];
      let position = 0;

      while (true) {
        const tagStart = xml.indexOf(marker, position);
        if (tagStart === -1) break;
        let contentStart = xml.indexOf('>', tagStart);
        if (contentStart === -1) break;
        contentStart += 1;
        const tagEnd = xml.indexOf(endMarker, contentStart);
        if (tagEnd === -1) break;

        const attrString = xml.substring(tagStart + marker.length, contentStart - 1);
        const content = xml.substring(contentStart, tagEnd);
        const start = marker === '<p '
          ? (parseFloat(getAttr(attrString, 't')) || 0) / 1000
          : (parseFloat(getAttr(attrString, 'start')) || 0);
        const duration = marker === '<p '
          ? (parseFloat(getAttr(attrString, 'd')) || 0) / 1000
          : (parseFloat(getAttr(attrString, 'dur')) || 0);
        const text = decodeEntities(content.replace(/<[^>]+>/g, '')).split('\\n').join(' ').trim();
        if (text) {
          results.push({ start, end: start + duration, text });
        }

        position = tagEnd + endMarker.length;
      }

      if (results.length === 0) {
        return { error: 'Parsed 0 transcript segments' };
      }
      return results;
    })()
  `);

  if (!Array.isArray(segments) || segments.length === 0) {
    context.log.debug("Parsed no YouTube transcript segments.");
    return null;
  }

  const extractedChapters = await context.browser.evaluate<YouTubeChapter[]>(`
    (() => {
      const data = window.ytInitialData;
      const markers = data?.playerOverlays?.playerOverlayRenderer
        ?.decoratedPlayerBarRenderer?.decoratedPlayerBarRenderer
        ?.playerBar?.multiMarkersPlayerBarRenderer?.markersMap || [];
      const results = [];

      for (const marker of markers) {
        const chapters = marker?.value?.chapters;
        if (!Array.isArray(chapters)) continue;
        for (const chapter of chapters) {
          const renderer = chapter?.chapterRenderer;
          const title = renderer?.title?.simpleText;
          const timeRangeStartMillis = renderer?.timeRangeStartMillis;
          if (title && typeof timeRangeStartMillis === 'number') {
            results.push({ title, time: Math.floor(timeRangeStartMillis / 1000) });
          }
        }
      }

      return results;
    })()
  `).catch(() => []);

  const descriptionChapters = parseYouTubeDescriptionChapters(captionInfo.description);
  const chapters = extractedChapters.length > 0 ? extractedChapters : descriptionChapters;
  const markdown = renderYouTubeTranscriptMarkdown({
    description: captionInfo.description,
    segments,
    chapters,
  });

  if (!markdown) {
    return null;
  }

  const pageUrl = await context.browser.getURL();
  const coverImage = await resolveBestCoverImage(videoId, captionInfo.coverImages);
  const summary = buildSummary(captionInfo.description, segments);

  return {
    url: pageUrl,
    canonicalUrl: pageUrl,
    title: captionInfo.title || "YouTube Transcript",
    author: captionInfo.author,
    publishedAt: captionInfo.publishedAt,
    siteName: "YouTube",
    summary,
    adapter: "youtube",
    metadata: {
      kind: "youtube/transcript",
      videoId,
      authorUrl: normalizeUrl(captionInfo.authorUrl),
      channelId: captionInfo.channelId,
      coverImage,
      description: captionInfo.description,
      durationSeconds: captionInfo.durationSeconds,
      language: captionInfo.language,
      captionKind: captionInfo.kind,
      availableLanguages: captionInfo.available,
      viewCount: captionInfo.viewCount,
      keywords: captionInfo.keywords,
      category: captionInfo.category,
      isLiveContent: captionInfo.isLiveContent,
      chapterCount: chapters.length,
    },
    content: [{ type: "markdown", markdown }],
  };
}
