export type Format = "text" | "srt";

export interface Options {
  videoIds: string[];
  languages: string[];
  format: Format;
  translate: string;
  list: boolean;
  excludeGenerated: boolean;
  excludeManual: boolean;
  output: string;
  outputDir: string;
  timestamps: boolean;
  chapters: boolean;
  speakers: boolean;
  refresh: boolean;
}

export interface Snippet {
  text: string;
  start: number;
  duration: number;
}

export interface Sentence {
  text: string;
  start: string;
  end: string;
}

export interface TranscriptLanguage {
  language: string;
  languageCode: string;
}

export interface TranscriptInfo {
  language: string;
  languageCode: string;
  isGenerated: boolean;
  isTranslatable: boolean;
  baseUrl: string;
  translationLanguages: TranscriptLanguage[];
}

export interface Chapter {
  title: string;
  start: number;
  end: number;
}

export interface LanguageMeta {
  code: string;
  name: string;
  isGenerated: boolean;
}

export interface VideoMeta {
  videoId: string;
  title: string;
  channel: string;
  channelId: string;
  description: string;
  duration: number;
  publishDate: string;
  url: string;
  coverImage: string;
  thumbnailUrl: string;
  language: LanguageMeta;
  chapters: Chapter[];
}

export interface VideoResult {
  videoId: string;
  title?: string;
  filePath?: string;
  content?: string;
  error?: string;
}

export interface InnerTubeSession {
  apiKey: string;
  webClientVersion: string;
  visitorData: string;
}

export interface InnerTubeClient {
  id: string;
  clientName: string;
  clientVersion?: string;
  clientHeaderName?: string;
  userAgent: string;
  extraContext?: Record<string, any>;
}

export interface TranscriptError extends Error {
  code?: string;
}

export interface YtDlpTrack {
  ext?: string;
  url?: string;
  name?: string;
}

export interface YtDlpInfo {
  title?: string;
  channel?: string;
  channel_id?: string;
  uploader?: string;
  uploader_id?: string;
  description?: string;
  duration?: number;
  upload_date?: string;
  webpage_url?: string;
  thumbnail?: string;
  thumbnails?: { url?: string; width?: number; height?: number }[];
  subtitles?: Record<string, YtDlpTrack[]>;
  automatic_captions?: Record<string, YtDlpTrack[]>;
}

export type VideoSource =
  | { kind: "innertube"; data: any; transcripts: TranscriptInfo[] }
  | { kind: "yt-dlp"; info: YtDlpInfo; transcripts: TranscriptInfo[] };
