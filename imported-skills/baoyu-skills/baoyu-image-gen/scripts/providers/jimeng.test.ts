import assert from "node:assert/strict";
import test, { type TestContext } from "node:test";

import type { CliArgs } from "../types.ts";
import { generateImage } from "./jimeng.ts";

function makeArgs(overrides: Partial<CliArgs> = {}): CliArgs {
  return {
    prompt: null,
    promptFiles: [],
    imagePath: null,
    provider: null,
    model: null,
    aspectRatio: null,
    size: null,
    quality: null,
    imageSize: null,
    imageApiDialect: null,
    referenceImages: [],
    n: 1,
    batchFile: null,
    jobs: null,
    json: false,
    help: false,
    ...overrides,
  };
}

function useEnv(
  t: TestContext,
  values: Record<string, string | null>,
): void {
  const previous = new Map<string, string | undefined>();
  for (const [key, value] of Object.entries(values)) {
    previous.set(key, process.env[key]);
    if (value == null) {
      delete process.env[key];
    } else {
      process.env[key] = value;
    }
  }

  t.after(() => {
    for (const [key, value] of previous.entries()) {
      if (value == null) {
        delete process.env[key];
      } else {
        process.env[key] = value;
      }
    }
  });
}

test("Jimeng submit request uses prompt field expected by current API", async (t) => {
  useEnv(t, {
    JIMENG_ACCESS_KEY_ID: "test-access-key",
    JIMENG_SECRET_ACCESS_KEY: "test-secret-key",
    JIMENG_BASE_URL: null,
    JIMENG_REGION: null,
  });

  const originalFetch = globalThis.fetch;
  t.after(() => {
    globalThis.fetch = originalFetch;
  });

  const calls: Array<{
    input: string;
    init?: RequestInit;
  }> = [];

  globalThis.fetch = async (input, init) => {
    calls.push({
      input: String(input),
      init,
    });

    if (calls.length === 1) {
      return Response.json({
        code: 10000,
        data: {
          task_id: "task-123",
        },
      });
    }

    return Response.json({
      code: 10000,
      data: {
        status: "done",
        binary_data_base64: [Buffer.from("jimeng-image").toString("base64")],
      },
    });
  };

  const image = await generateImage(
    "A quiet bamboo forest",
    "jimeng_t2i_v40",
    makeArgs({ quality: "normal" }),
  );

  assert.equal(Buffer.from(image).toString("utf8"), "jimeng-image");
  assert.equal(calls.length, 2);
  assert.equal(
    calls[0]?.input,
    "https://visual.volcengineapi.com/?Action=CVSync2AsyncSubmitTask&Version=2022-08-31",
  );

  const submitBody = JSON.parse(String(calls[0]?.init?.body)) as Record<string, unknown>;
  assert.equal(submitBody.req_key, "jimeng_t2i_v40");
  assert.equal(submitBody.prompt, "A quiet bamboo forest");
  assert.ok(!("prompt_text" in submitBody));
  assert.equal(submitBody.width, 1024);
  assert.equal(submitBody.height, 1024);
});
