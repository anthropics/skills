import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const articleScript = fs.readFileSync(path.join(__dirname, "wechat-article.ts"), "utf8");

test("browser article paste uses CDP-targeted paste instead of global macOS keystrokes", () => {
  assert.equal(
    articleScript.includes('tell application "System Events" to keystroke "v" using command down'),
    false,
  );
});

test("browser article publishing verifies the title before saving drafts", () => {
  assert.match(articleScript, /verifyTitleUnchangedBeforeSave/);
  assert.match(articleScript, /Title was modified during paste/);
});

test("browser article body insertion does not paste HTML through the active form field", () => {
  assert.match(articleScript, /insertHtmlIntoEditorFromFile/);
  assert.doesNotMatch(articleScript, /await copyHtmlFromBrowser\(cdp, effectiveHtmlFile, contentImages\)/);
});

test("browser article body operations target the body ProseMirror, not the title ProseMirror", () => {
  assert.match(articleScript, /BODY_EDITOR_SELECTOR = '\.rich_media_content \.ProseMirror'/);
  assert.doesNotMatch(articleScript, /clickElement\(session, '\\.ProseMirror'\)/);
});

test("browser article reuses the selected account Chrome profile before launching", () => {
  assert.match(articleScript, /await findExistingChromeDebugPort\(profileDir\)/);
});

test("browser article inserts inline images through WeChat local upload instead of clipboard paste", () => {
  assert.match(articleScript, /uploadImageThroughFileInput/);
  assert.match(articleScript, /DOM\.setFileInputFiles/);
  assert.doesNotMatch(articleScript, /await copyImageToClipboard\(img\.localPath\)/);
});

test("browser article uploads original images before fallback processing", () => {
  const rawUploadIndex = articleScript.indexOf("await uploadImagePathThroughFileInput(session, absolutePath, beforeCount)");
  const fallbackIndex = articleScript.indexOf("const fallback = await prepareFallbackWechatBodyImageUpload(absolutePath)");

  assert.notEqual(rawUploadIndex, -1);
  assert.notEqual(fallbackIndex, -1);
  assert.ok(rawUploadIndex < fallbackIndex);
  assert.match(articleScript, /prepareWechatBodyImageUpload/);
  assert.match(articleScript, /Raw image upload failed, retrying with fallback processing/);
});

test("browser article waits for a saved draft appmsgid before reporting success", () => {
  assert.match(articleScript, /waitForDraftSaved/);
  assert.match(articleScript, /appmsgid/);
  assert.doesNotMatch(articleScript, /Waiting for save confirmation/);
});
