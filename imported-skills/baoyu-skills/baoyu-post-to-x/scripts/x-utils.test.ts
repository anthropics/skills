import assert from "node:assert/strict";
import test from "node:test";

import {
  buildXSessionCookieMap,
  hasChromeLockArtifacts,
  hasRequiredXSessionCookies,
  shouldRetryChromeLaunch,
} from "./x-utils.ts";

test("hasChromeLockArtifacts detects Chrome singleton artifacts", () => {
  assert.equal(hasChromeLockArtifacts(["SingletonSocket"]), true);
  assert.equal(hasChromeLockArtifacts(["chrome.pid"]), true);
  assert.equal(hasChromeLockArtifacts(["Cookies", "Preferences"]), false);
});

test("shouldRetryChromeLaunch only retries when no live owner exists", () => {
  assert.equal(
    shouldRetryChromeLaunch({ lockArtifactsPresent: true, hasLiveOwner: false }),
    true,
  );
  assert.equal(
    shouldRetryChromeLaunch({ lockArtifactsPresent: true, hasLiveOwner: true }),
    false,
  );
  assert.equal(
    shouldRetryChromeLaunch({ lockArtifactsPresent: false, hasLiveOwner: false }),
    false,
  );
});

test("buildXSessionCookieMap keeps only non-empty cookies", () => {
  assert.deepEqual(
    buildXSessionCookieMap([
      { name: "auth_token", value: "auth" },
      { name: "ct0", value: "csrf" },
      { name: "twid", value: "u=123" },
      { name: "ct0", value: "" },
      { name: "", value: "ignored" },
      { name: "gt", value: undefined },
    ]),
    {
      auth_token: "auth",
      ct0: "csrf",
      twid: "u=123",
    },
  );
});

test("hasRequiredXSessionCookies requires auth_token and ct0", () => {
  assert.equal(hasRequiredXSessionCookies({ auth_token: "auth" }), false);
  assert.equal(hasRequiredXSessionCookies({ ct0: "csrf" }), false);
  assert.equal(hasRequiredXSessionCookies({ auth_token: "auth", ct0: "csrf" }), true);
});
