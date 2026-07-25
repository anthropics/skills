export type Provider =
  | "google"
  | "openai"
  | "openrouter"
  | "dashscope"
  | "zai"
  | "minimax"
  | "replicate"
  | "jimeng"
  | "seedream"
  | "azure"
  | "codex-cli"
  | "agnes";
export type Quality = "normal" | "2k";
export type OpenAIImageApiDialect = "openai-native" | "ratio-metadata";
export type ResponseFormat = "file" | "url";

export type CliArgs = {
  prompt: string | null;
  promptFiles: string[];
  imagePath: string | null;
  provider: Provider | null;
  model: string | null;
  aspectRatio: string | null;
  aspectRatioSource?: "cli" | "task" | "config" | null;
  size: string | null;
  quality: Quality | null;
  imageSize: string | null;
  imageSizeSource?: "cli" | "task" | "config" | null;
  imageApiDialect: OpenAIImageApiDialect | null;
  responseFormat: ResponseFormat | null;
  referenceImages: string[];
  n: number;
  batchFile: string | null;
  jobs: number | null;
  json: boolean;
  help: boolean;
};

export type BatchTaskInput = {
  id?: string;
  prompt?: string | null;
  promptFiles?: string[];
  image?: string;
  provider?: Provider | null;
  model?: string | null;
  ar?: string | null;
  size?: string | null;
  quality?: Quality | null;
  imageSize?: "1K" | "2K" | "4K" | null;
  imageApiDialect?: OpenAIImageApiDialect | null;
  responseFormat?: ResponseFormat | null;
  ref?: string[];
  n?: number;
};

export type BatchFile =
  | BatchTaskInput[]
  | {
      tasks: BatchTaskInput[];
      jobs?: number | null;
    };

export type ExtendConfig = {
  version: number;
  default_provider: Provider | null;
  default_quality: Quality | null;
  default_aspect_ratio: string | null;
  default_image_size: "1K" | "2K" | "4K" | null;
  default_image_api_dialect: OpenAIImageApiDialect | null;
  default_model: {
    google: string | null;
    openai: string | null;
    openrouter: string | null;
    dashscope: string | null;
    zai: string | null;
    minimax: string | null;
    replicate: string | null;
    jimeng: string | null;
    seedream: string | null;
    azure: string | null;
    "codex-cli": string | null;
    agnes: string | null;
  };
  batch?: {
    max_workers?: number | null;
    provider_limits?: Partial<
      Record<
        Provider,
        {
          concurrency?: number | null;
          start_interval_ms?: number | null;
        }
      >
    >;
  };
};
