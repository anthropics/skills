import assert from "node:assert/strict";
import test from "node:test";

import { collect_generated_image_urls_from_response_parts } from "./client.ts";

test("response part fallback finds generated images when legacy generated markers are absent", () => {
  const generatedUrl = "https://lh3.googleusercontent.com/gg-dl/example-generated-image";
  const initialCandidate = ["rcid-1", ["image generated successfully"]];
  const imageCandidate = [
    "rcid-1",
    ["image generated successfully"],
    { nestedPayload: [{ media: generatedUrl }] },
  ];
  const responseJson = [
    ["wrb.fr", null, JSON.stringify([null, [], null, null, [initialCandidate]])],
    ["wrb.fr", null, JSON.stringify([null, [], null, null, [imageCandidate]])],
  ];

  assert.equal(initialCandidate[12], undefined);
  assert.equal(
    /http:\/\/googleusercontent\.com\/image_generation_content\/\d+/.test(String(initialCandidate[1]?.[0])),
    false,
  );
  assert.deepEqual(collect_generated_image_urls_from_response_parts(responseJson, 0, 0), [generatedUrl]);
});
