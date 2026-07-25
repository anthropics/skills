import type { Adapter } from "../types";
import { collectMediaFromDocument } from "../../media/markdown-media";
import { extractYouTubeTranscriptDocument } from "./transcript";
import { isYouTubeHost, parseYouTubeVideoId } from "./utils";

export const youtubeAdapter: Adapter = {
  name: "youtube",
  match(input) {
    return isYouTubeHost(input.url.hostname);
  },
  async process(context) {
    const videoId = parseYouTubeVideoId(context.input.url);
    if (!videoId) {
      return {
        status: "no_document",
      };
    }

    context.log.info(`Loading ${context.input.url.toString()} with youtube adapter`);
    const document = await extractYouTubeTranscriptDocument(context, videoId);
    if (!document) {
      return {
        status: "no_document",
      };
    }

    return {
      status: "ok",
      document,
      media: collectMediaFromDocument(document),
    };
  },
};
