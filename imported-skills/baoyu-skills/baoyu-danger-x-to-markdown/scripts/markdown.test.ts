import assert from "node:assert/strict";
import test from "node:test";

import { formatArticleMarkdown } from "./markdown.js";

test("formatArticleMarkdown renders MARKDOWN entities from atomic blocks", () => {
  const article = {
    title: "Atomic Markdown Example",
    content_state: {
      blocks: [
        {
          type: "unstyled",
          text: "Before the snippet.",
          entityRanges: [],
        },
        {
          type: "atomic",
          text: " ",
          entityRanges: [{ key: 0, offset: 0, length: 1 }],
        },
        {
          type: "unstyled",
          text: "After the snippet.",
          entityRanges: [],
        },
      ],
      entityMap: {
        "0": {
          key: "5",
          value: {
            type: "MARKDOWN",
            mutability: "Mutable",
            data: {
              markdown: "```python\nprint('hello from x article')\n```\n",
            },
          },
        },
      },
    },
  };

  const { markdown } = formatArticleMarkdown(article);

  assert.ok(markdown.includes("Before the snippet."));
  assert.ok(markdown.includes("```python\nprint('hello from x article')\n```"));
  assert.ok(markdown.includes("After the snippet."));
  assert.strictEqual(markdown, `# Atomic Markdown Example

Before the snippet.

\`\`\`python
print('hello from x article')
\`\`\`

After the snippet.`);
});

test("formatArticleMarkdown renders article video media as poster plus video link", () => {
  const posterUrl = "https://pbs.twimg.com/amplify_video_thumb/123/img/poster.jpg";
  const videoUrl = "https://video.twimg.com/amplify_video/123/vid/avc1/720x720/demo.mp4?tag=21";
  const article = {
    title: "Video Example",
    content_state: {
      blocks: [
        {
          type: "unstyled",
          text: "Intro text.",
          entityRanges: [],
        },
        {
          type: "atomic",
          text: " ",
          entityRanges: [{ key: 0, offset: 0, length: 1 }],
        },
      ],
      entityMap: {
        "0": {
          key: "0",
          value: {
            type: "MEDIA",
            mutability: "Immutable",
            data: {
              caption: "Demo reel",
              mediaItems: [{ mediaId: "vid-1" }],
            },
          },
        },
      },
    },
    media_entities: [
      {
        media_id: "vid-1",
        media_info: {
          __typename: "ApiVideo",
          preview_image: {
            original_img_url: posterUrl,
          },
          variants: [
            {
              content_type: "video/mp4",
              bit_rate: 256000,
              url: videoUrl,
            },
          ],
        },
      },
    ],
  };

  const { markdown } = formatArticleMarkdown(article);

  assert.ok(markdown.includes("Intro text."));
  assert.ok(markdown.includes(`![Demo reel](${posterUrl})`));
  assert.ok(markdown.includes(`[video](${videoUrl})`));
  assert.ok(!markdown.includes(`![Demo reel](${videoUrl})`));
  assert.ok(!markdown.includes("## Media"));
});

test("formatArticleMarkdown renders unused article videos in trailing media section", () => {
  const posterUrl = "https://pbs.twimg.com/amplify_video_thumb/456/img/poster.jpg";
  const videoUrl = "https://video.twimg.com/amplify_video/456/vid/avc1/1080x1080/demo.mp4?tag=21";
  const article = {
    title: "Trailing Media Example",
    plain_text: "Body text.",
    media_entities: [
      {
        media_id: "vid-2",
        media_info: {
          __typename: "ApiVideo",
          preview_image: {
            original_img_url: posterUrl,
          },
          variants: [
            {
              content_type: "video/mp4",
              bit_rate: 832000,
              url: videoUrl,
            },
          ],
        },
      },
    ],
  };

  const { markdown, coverUrl } = formatArticleMarkdown(article);

  assert.strictEqual(coverUrl, null);
  assert.ok(markdown.includes("## Media"));
  assert.ok(markdown.includes(`![video](${posterUrl})`));
  assert.ok(markdown.includes(`[video](${videoUrl})`));
});

test("formatArticleMarkdown keeps coverUrl as preview image for video cover media", () => {
  const posterUrl = "https://pbs.twimg.com/amplify_video_thumb/789/img/poster.jpg";
  const videoUrl = "https://video.twimg.com/amplify_video/789/vid/avc1/720x720/demo.mp4?tag=21";
  const article = {
    title: "Video Cover Example",
    plain_text: "Body text.",
    cover_media: {
      media_info: {
        __typename: "ApiVideo",
        preview_image: {
          original_img_url: posterUrl,
        },
        variants: [
          {
            content_type: "video/mp4",
            bit_rate: 1280000,
            url: videoUrl,
          },
        ],
      },
    },
  };

  const { coverUrl } = formatArticleMarkdown(article);

  assert.strictEqual(coverUrl, posterUrl);
});
