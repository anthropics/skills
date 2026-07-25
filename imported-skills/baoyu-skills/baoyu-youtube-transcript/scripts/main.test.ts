import test from "node:test";
import assert from "node:assert/strict";

import { findTranscript, parseTranscriptJson3, parseWebVtt } from "./transcript.ts";
import { buildTranscriptListFromYtDlp, fetchTranscriptWithFallback, resolveVideoSource, selectYtDlpTrack } from "./youtube.ts";

test("selectYtDlpTrack prefers json3 over xml and vtt", () => {
  const track = selectYtDlpTrack([
    { ext: "vtt", url: "https://example.com/subs.vtt" },
    { ext: "srv3", url: "https://example.com/subs.srv3" },
    { ext: "json3", url: "https://example.com/subs.json3" },
  ]);

  assert.equal(track?.ext, "json3");
});

test("buildTranscriptListFromYtDlp keeps manual and generated tracks separate", () => {
  const transcripts = buildTranscriptListFromYtDlp({
    subtitles: {
      en: [
        { ext: "json3", url: "https://example.com/en.json3", name: "English" },
      ],
    },
    automatic_captions: {
      "zh-Hans": [
        { ext: "json3", url: "https://example.com/zh.json3", name: "Chinese (Simplified)" },
      ],
    },
  });

  assert.equal(transcripts.length, 2);
  assert.equal(transcripts[0].isGenerated, false);
  assert.equal(transcripts[1].isGenerated, true);
  assert.equal(transcripts[0].translationLanguages[0]?.languageCode, "zh-Hans");

  const translated = findTranscript(transcripts, ["zh-Hans"], false, false);
  assert.equal(translated.languageCode, "zh-Hans");
  assert.equal(translated.isGenerated, true);
});

test("parseTranscriptJson3 reads youtube timedtext json3 payloads", () => {
  const snippets = parseTranscriptJson3(JSON.stringify({
    events: [
      {
        tStartMs: 80,
        dDurationMs: 3120,
        segs: [{ utf8: "hello\nworld" }],
      },
      {
        tStartMs: 4000,
        dDurationMs: 1800,
        segs: [{ utf8: "again" }],
      },
    ],
  }));

  assert.deepEqual(snippets, [
    { text: "hello world", start: 0.08, duration: 3.12 },
    { text: "again", start: 4, duration: 1.8 },
  ]);
});

test("parseWebVtt strips tags and cue settings", () => {
  const snippets = parseWebVtt(`WEBVTT

00:00:00.080 --> 00:00:03.200 align:start position:0%
<c.colorE5E5E5>Hello</c> world

00:00:04.000 --> 00:00:05.800
Again
`);

  assert.equal(snippets.length, 2);
  assert.equal(snippets[0].text, "Hello world");
  assert.equal(snippets[0].start, 0.08);
  assert.equal(snippets[0].duration, 3.12);
  assert.equal(snippets[1].text, "Again");
  assert.equal(snippets[1].start, 4);
  assert.equal(Number(snippets[1].duration.toFixed(1)), 1.8);
});

test("resolveVideoSource prefers primary InnerTube result before fallback", async () => {
  let fallbackCalled = false;
  const source = await resolveVideoSource(
    "video12345ab",
    async () => ({ kind: "innertube", data: { videoDetails: { title: "Primary" } }, transcripts: [] }),
    () => {
      fallbackCalled = true;
      return {
        subtitles: {
          en: [{ ext: "json3", url: "https://example.com/en.json3", name: "English" }],
        },
      };
    },
    () => {}
  );

  assert.equal(source.kind, "innertube");
  assert.equal(fallbackCalled, false);
});

test("resolveVideoSource falls back to yt-dlp only after fallback-eligible errors", async () => {
  let fallbackCalled = false;
  const source = await resolveVideoSource(
    "video12345ab",
    async () => {
      const error = new Error("Request blocked for video12345ab: bot detected");
      (error as Error & { code?: string }).code = "BOT_DETECTED";
      throw error;
    },
    () => {
      fallbackCalled = true;
      return {
        automatic_captions: {
          en: [{ ext: "json3", url: "https://example.com/en.json3", name: "English (auto-generated)" }],
        },
      };
    },
    () => {}
  );

  assert.equal(source.kind, "yt-dlp");
  assert.equal(fallbackCalled, true);
  assert.equal(source.transcripts[0].languageCode, "en");
});

test("fetchTranscriptWithFallback retries with yt-dlp when InnerTube transcript payload is empty", async () => {
  const warnings: string[] = [];
  let fallbackCalled = false;
  const result = await fetchTranscriptWithFallback(
    "video12345ab",
    {
      kind: "innertube",
      data: { videoDetails: { title: "Primary" } },
      transcripts: [{
        language: "English",
        languageCode: "en",
        isGenerated: false,
        isTranslatable: false,
        baseUrl: "https://www.youtube.com/api/timedtext?v=video12345ab&lang=en&fmt=json3",
        translationLanguages: [],
      }],
    },
    {
      languages: ["en"],
      translate: "",
      excludeGenerated: false,
      excludeManual: false,
    },
    async (info) => {
      if (info.baseUrl.includes("youtube.com/api/timedtext")) {
        return { snippets: [], language: info.language, languageCode: info.languageCode };
      }
      return {
        snippets: [{ text: "Recovered subtitle", start: 0, duration: 2 }],
        language: info.language,
        languageCode: info.languageCode,
      };
    },
    async () => {
      fallbackCalled = true;
      return {
        kind: "yt-dlp",
        info: { title: "Fallback" },
        transcripts: [{
          language: "English",
          languageCode: "en",
          isGenerated: false,
          isTranslatable: false,
          baseUrl: "https://example.com/subtitles.en.json3",
          translationLanguages: [],
        }],
      };
    },
    (message) => warnings.push(message)
  );

  assert.equal(fallbackCalled, true);
  assert.equal(result.source.kind, "yt-dlp");
  assert.equal(result.snippets.length, 1);
  assert.equal(result.snippets[0].text, "Recovered subtitle");
  assert.match(warnings[0] || "", /Retrying with yt-dlp fallback/);
});
