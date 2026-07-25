import fs from 'node:fs';
import { mkdir, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';

import { parseMarkdown } from './md-to-html.js';
import {
  CHROME_CANDIDATES_BASIC,
  CdpConnection,
  copyHtmlToClipboard,
  copyImageToClipboard,
  findExistingChromeDebugPort,
  getDefaultProfileDir,
  launchChrome,
  openPageSession,
  pasteFromClipboard,
  sleep,
  waitForChromeDebugPort,
} from './x-utils.js';

const X_ARTICLES_URL = 'https://x.com/compose/articles';

const I18N_SELECTORS = {
  titleInput: [
    'textarea[placeholder="Add a title"]',
    'textarea[placeholder="添加标题"]',
    'textarea[placeholder="タイトルを追加"]',
    'textarea[placeholder="제목 추가"]',
    'textarea[name="Article Title"]',
  ],
  addPhotosButton: [
    '[aria-label="Add photos or video"]',
    '[aria-label="添加照片或视频"]',
    '[aria-label="写真や動画を追加"]',
    '[aria-label="사진 또는 동영상 추가"]',
  ],
  previewButton: [
    'a[href*="/preview"]',
    '[data-testid="previewButton"]',
    'button[aria-label*="preview" i]',
    'button[aria-label*="预览" i]',
    'button[aria-label*="プレビュー" i]',
    'button[aria-label*="미리보기" i]',
  ],
  publishButton: [
    '[data-testid="publishButton"]',
    'button[aria-label*="publish" i]',
    'button[aria-label*="发布" i]',
    'button[aria-label*="公開" i]',
    'button[aria-label*="게시" i]',
  ],
};

interface ArticleOptions {
  markdownPath: string;
  coverImage?: string;
  title?: string;
  submit?: boolean;
  profileDir?: string;
  chromePath?: string;
}

export async function publishArticle(options: ArticleOptions): Promise<void> {
  const { markdownPath, submit = false, profileDir = getDefaultProfileDir() } = options;

  console.log('[x-article] Parsing markdown...');
  const parsed = await parseMarkdown(markdownPath, {
    title: options.title,
    coverImage: options.coverImage,
  });

  console.log(`[x-article] Title: ${parsed.title}`);
  console.log(`[x-article] Cover: ${parsed.coverImage ?? 'none'}`);
  console.log(`[x-article] Content images: ${parsed.contentImages.length}`);

  // Save HTML to temp file
  const htmlPath = path.join(os.tmpdir(), 'x-article-content.html');
  await writeFile(htmlPath, parsed.html, 'utf-8');
  console.log(`[x-article] HTML saved to: ${htmlPath}`);

  await mkdir(profileDir, { recursive: true });
  const existingPort = await findExistingChromeDebugPort(profileDir);
  const reusing = existingPort !== null;
  let port = existingPort ?? 0;

  if (reusing) {
    console.log(`[x-article] Reusing existing Chrome instance on port ${port}`);
  } else {
    console.log(`[x-article] Launching Chrome...`);
    const launched = await launchChrome(X_ARTICLES_URL, profileDir, CHROME_CANDIDATES_BASIC, options.chromePath);
    port = launched.port;
  }

  let cdp: CdpConnection | null = null;

  try {
    const wsUrl = await waitForChromeDebugPort(port, 30_000, { includeLastError: true });
    cdp = await CdpConnection.connect(wsUrl, 30_000, { defaultTimeoutMs: 60_000 });

    const page = await openPageSession({
      cdp,
      reusing,
      url: X_ARTICLES_URL,
      matchTarget: (target) => target.type === 'page' && target.url.startsWith(X_ARTICLES_URL),
      enablePage: true,
      enableRuntime: true,
      enableDom: true,
    });
    const { sessionId } = page;

    console.log('[x-article] Waiting for articles page...');
    await sleep(1000);

    // Wait for and click "create" button
    const waitForElement = async (selector: string, timeoutMs = 60_000): Promise<boolean> => {
      const start = Date.now();
      while (Date.now() - start < timeoutMs) {
        const result = await cdp!.send<{ result: { value: boolean } }>('Runtime.evaluate', {
          expression: `!!document.querySelector('${selector}')`,
          returnByValue: true,
        }, { sessionId });
        if (result.result.value) return true;
        await sleep(500);
      }
      return false;
    };

    const clickElement = async (selector: string): Promise<boolean> => {
      const result = await cdp!.send<{ result: { value: boolean } }>('Runtime.evaluate', {
        expression: `(() => { const el = document.querySelector('${selector}'); if (el) { el.click(); return true; } return false; })()`,
        returnByValue: true,
      }, { sessionId });
      return result.result.value;
    };

    const typeText = async (selector: string, text: string): Promise<void> => {
      await cdp!.send('Runtime.evaluate', {
        expression: `(() => {
          const el = document.querySelector('${selector}');
          if (el) {
            el.focus();
            document.execCommand('insertText', false, ${JSON.stringify(text)});
          }
        })()`,
      }, { sessionId });
    };

    const pressKey = async (key: string, modifiers = 0): Promise<void> => {
      await cdp!.send('Input.dispatchKeyEvent', {
        type: 'keyDown',
        key,
        code: `Key${key.toUpperCase()}`,
        modifiers,
        windowsVirtualKeyCode: key.toUpperCase().charCodeAt(0),
      }, { sessionId });
      await cdp!.send('Input.dispatchKeyEvent', {
        type: 'keyUp',
        key,
        code: `Key${key.toUpperCase()}`,
        modifiers,
        windowsVirtualKeyCode: key.toUpperCase().charCodeAt(0),
      }, { sessionId });
    };

    // Check if we're on the articles list page (has Write button)
    console.log('[x-article] Looking for Write button...');
    const writeButtonFound = await waitForElement('[data-testid="empty_state_button_text"]', 30_000);

    if (writeButtonFound) {
      console.log('[x-article] Clicking Write button...');
      await cdp.send('Runtime.evaluate', {
        expression: `document.querySelector('[data-testid="empty_state_button_text"]')?.click()`,
      }, { sessionId });
      await sleep(2000);
    } else {
      console.log('[x-article] Write button not found, looking for create button...');
      const createClicked = await cdp.send<{ result: { value: boolean } }>('Runtime.evaluate', {
        expression: `(() => {
          const selectors = [
            'button[aria-label="create"]',
            'button[aria-label="Create"]',
            'button[aria-label*="create" i]',
            'button[aria-label*="write" i]',
            'a[href="/compose/articles"]'
          ];
          for (const sel of selectors) {
            const el = document.querySelector(sel);
            if (el instanceof HTMLElement) {
              el.click();
              return true;
            }
          }
          const buttons = [...document.querySelectorAll('button')];
          const byText = buttons.find((el) => /^(create|write)$/i.test((el.textContent || '').trim()));
          if (byText instanceof HTMLElement) {
            byText.click();
            return true;
          }
          return false;
        })()`,
        returnByValue: true,
      }, { sessionId });
      if (createClicked.result.value) {
        console.log('[x-article] Create button clicked');
        await sleep(2000);
      } else {
        console.log('[x-article] Create button not found');
      }
    }

    // Wait for editor (title textarea)
    const titleSelectors = I18N_SELECTORS.titleInput.join(', ');
    console.log('[x-article] Waiting for editor...');
    const editorFound = await waitForElement(titleSelectors, 30_000);
    if (!editorFound) {
      console.log('[x-article] Editor not found. Please ensure you have X Premium and are logged in.');
      await sleep(60_000);
      throw new Error('Editor not found');
    }

    // Upload cover image
    if (parsed.coverImage) {
      console.log('[x-article] Uploading cover image...');

      // Click "Add photos or video" button
      const addPhotosSelectors = JSON.stringify(I18N_SELECTORS.addPhotosButton);
      await cdp.send('Runtime.evaluate', {
        expression: `(() => {
          const selectors = ${addPhotosSelectors};
          for (const sel of selectors) {
            const el = document.querySelector(sel);
            if (el) { el.click(); return true; }
          }
          return false;
        })()`,
      }, { sessionId });
      await sleep(500);

      // Use file input directly
      const { root } = await cdp.send<{ root: { nodeId: number } }>('DOM.getDocument', {}, { sessionId });
      const { nodeId } = await cdp.send<{ nodeId: number }>('DOM.querySelector', {
        nodeId: root.nodeId,
        selector: '[data-testid="fileInput"], input[type="file"][accept*="image"]',
      }, { sessionId });

      if (nodeId) {
        await cdp.send('DOM.setFileInputFiles', {
          nodeId,
          files: [parsed.coverImage],
        }, { sessionId });
        console.log('[x-article] Cover image file set');

        // Wait for Apply button to appear and click it
        console.log('[x-article] Waiting for Apply button...');
        const applyFound = await waitForElement('[data-testid="applyButton"]', 15_000);
        if (applyFound) {
          // Check if modal is present
          const isModalOpen = async (): Promise<boolean> => {
            const result = await cdp!.send<{ result: { value: boolean } }>('Runtime.evaluate', {
              expression: `!!document.querySelector('[role="dialog"][aria-modal="true"]')`,
              returnByValue: true,
            }, { sessionId });
            return result.result.value;
          };

          // Click Apply button with retry logic
          const maxRetries = 3;
          for (let attempt = 1; attempt <= maxRetries; attempt++) {
            console.log(`[x-article] Clicking Apply button (attempt ${attempt}/${maxRetries})...`);

            await cdp.send('Runtime.evaluate', {
              expression: `document.querySelector('[data-testid="applyButton"]')?.click()`,
            }, { sessionId });

            // Wait for modal to close (up to 5 seconds per attempt)
            const closeTimeout = 5000;
            const checkInterval = 300;
            const startTime = Date.now();
            let modalClosed = false;

            while (Date.now() - startTime < closeTimeout) {
              await sleep(checkInterval);
              const stillOpen = await isModalOpen();
              if (!stillOpen) {
                modalClosed = true;
                break;
              }
            }

            if (modalClosed) {
              console.log('[x-article] Cover image applied, modal closed');
              await sleep(500);
              break;
            }

            if (attempt < maxRetries) {
              console.log('[x-article] Modal still open, retrying...');
            } else {
              console.log('[x-article] Modal did not close after all attempts, continuing anyway...');
            }
          }
        } else {
          console.log('[x-article] Apply button not found, continuing...');
        }
      }
    }

    // Fill title using keyboard input
    if (parsed.title) {
      console.log('[x-article] Filling title...');

      // Focus title input
      const titleInputSelectors = JSON.stringify(I18N_SELECTORS.titleInput);
      await cdp.send('Runtime.evaluate', {
        expression: `(() => {
          const selectors = ${titleInputSelectors};
          for (const sel of selectors) {
            const el = document.querySelector(sel);
            if (el) { el.focus(); return true; }
          }
          return false;
        })()`,
      }, { sessionId });
      await sleep(200);

      // Type title character by character using insertText
      await cdp.send('Input.insertText', { text: parsed.title }, { sessionId });
      await sleep(300);

      // Tab out to trigger save
      await cdp.send('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Tab', code: 'Tab', windowsVirtualKeyCode: 9 }, { sessionId });
      await cdp.send('Input.dispatchKeyEvent', { type: 'keyUp', key: 'Tab', code: 'Tab', windowsVirtualKeyCode: 9 }, { sessionId });
      await sleep(500);
    }

    // Insert HTML content
    console.log('[x-article] Inserting content...');

    // Read HTML content
    const htmlContent = fs.readFileSync(htmlPath, 'utf-8');

    // Focus on DraftEditor body
    await cdp.send('Runtime.evaluate', {
      expression: `(() => {
        const editor = document.querySelector('.DraftEditor-editorContainer [contenteditable="true"]');
        if (editor) {
          editor.focus();
          editor.click();
          return true;
        }
        return false;
      })()`,
    }, { sessionId });
    await sleep(300);

    // Method 1: Simulate paste event with HTML data
    console.log('[x-article] Attempting to insert HTML via paste event...');
    const pasteResult = await cdp.send<{ result: { value: boolean } }>('Runtime.evaluate', {
      expression: `(() => {
        const editor = document.querySelector('.DraftEditor-editorContainer [contenteditable="true"]');
        if (!editor) return false;

        const html = ${JSON.stringify(htmlContent)};

        // Create a paste event with HTML data
        const dt = new DataTransfer();
        dt.setData('text/html', html);
        dt.setData('text/plain', html.replace(/<[^>]*>/g, ''));

        const pasteEvent = new ClipboardEvent('paste', {
          bubbles: true,
          cancelable: true,
          clipboardData: dt
        });

        editor.dispatchEvent(pasteEvent);
        return true;
      })()`,
      returnByValue: true,
    }, { sessionId });

    await sleep(1000);

    // Check if content was inserted
    const contentCheck = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
      expression: `document.querySelector('.DraftEditor-editorContainer [data-contents="true"]')?.innerText?.length || 0`,
      returnByValue: true,
    }, { sessionId });

    if (contentCheck.result.value > 50) {
      console.log(`[x-article] Content inserted successfully (${contentCheck.result.value} chars)`);
    } else {
      console.log('[x-article] Paste event may not have worked, trying insertHTML...');

      // Method 2: Use execCommand insertHTML
      await cdp.send('Runtime.evaluate', {
        expression: `(() => {
          const editor = document.querySelector('.DraftEditor-editorContainer [contenteditable="true"]');
          if (!editor) return false;
          editor.focus();
          document.execCommand('insertHTML', false, ${JSON.stringify(htmlContent)});
          return true;
        })()`,
      }, { sessionId });

      await sleep(1000);

      // Check again
      const check2 = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
        expression: `document.querySelector('.DraftEditor-editorContainer [data-contents="true"]')?.innerText?.length || 0`,
        returnByValue: true,
      }, { sessionId });

      if (check2.result.value > 50) {
        console.log(`[x-article] Content inserted via execCommand (${check2.result.value} chars)`);
      } else {
        console.log('[x-article] Auto-insert failed. HTML copied to clipboard - please paste manually (Cmd+V)');
        copyHtmlToClipboard(htmlPath);
        // Wait for manual paste
        console.log('[x-article] Waiting 30s for manual paste...');
        await sleep(30_000);
      }
    }

    // Insert content images (reverse order to maintain positions)
    if (parsed.contentImages.length > 0) {
      console.log('[x-article] Inserting content images...');

      // First, check what placeholders exist in the editor
      const editorContent = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
        expression: `document.querySelector('.DraftEditor-editorContainer [data-contents="true"]')?.innerText || ''`,
        returnByValue: true,
      }, { sessionId });

      console.log('[x-article] Checking for placeholders in content...');
      for (const img of parsed.contentImages) {
        // Use regex for exact match (not followed by digit, e.g., XIMGPH_1 should not match XIMGPH_10)
        const regex = new RegExp(img.placeholder + '(?!\\d)');
        if (regex.test(editorContent.result.value)) {
          console.log(`[x-article] Found: ${img.placeholder}`);
        } else {
          console.log(`[x-article] NOT found: ${img.placeholder}`);
        }
      }

      // Process images in XIMGPH order (1, 2, 3, ...) regardless of blockIndex
      const getPlaceholderIndex = (placeholder: string): number => {
        const match = placeholder.match(/XIMGPH_(\d+)/);
        return match ? Number(match[1]) : Number.POSITIVE_INFINITY;
      };
      const sortedImages = [...parsed.contentImages].sort(
        (a, b) => getPlaceholderIndex(a.placeholder) - getPlaceholderIndex(b.placeholder),
      );

      for (let i = 0; i < sortedImages.length; i++) {
        const img = sortedImages[i]!;
        console.log(`[x-article] [${i + 1}/${sortedImages.length}] Inserting image at placeholder: ${img.placeholder}`);

        // Helper to select placeholder with retry
        const selectPlaceholder = async (maxRetries = 3): Promise<boolean> => {
          for (let attempt = 1; attempt <= maxRetries; attempt++) {
            // Find, scroll to, and select the placeholder text in DraftEditor
            await cdp!.send('Runtime.evaluate', {
              expression: `(() => {
                const editor = document.querySelector('.DraftEditor-editorContainer [data-contents="true"]');
                if (!editor) return false;

                const placeholder = ${JSON.stringify(img.placeholder)};

                // Search through all text nodes in the editor
                const walker = document.createTreeWalker(editor, NodeFilter.SHOW_TEXT, null, false);
                let node;

                while ((node = walker.nextNode())) {
                  const text = node.textContent || '';
                  let searchStart = 0;
                  let idx;
                  // Search for exact match (not prefix of longer placeholder like XIMGPH_1 in XIMGPH_10)
                  while ((idx = text.indexOf(placeholder, searchStart)) !== -1) {
                    const afterIdx = idx + placeholder.length;
                    const charAfter = text[afterIdx];
                    // Exact match if next char is not a digit (XIMGPH_1 should not match XIMGPH_10)
                    if (charAfter === undefined || !/\\d/.test(charAfter)) {
                      // Found exact placeholder - scroll to it first
                      const parentElement = node.parentElement;
                      if (parentElement) {
                        parentElement.scrollIntoView({ behavior: 'smooth', block: 'center' });
                      }

                      // Select it
                      const range = document.createRange();
                      range.setStart(node, idx);
                      range.setEnd(node, idx + placeholder.length);
                      const sel = window.getSelection();
                      sel.removeAllRanges();
                      sel.addRange(range);
                      return true;
                    }
                    searchStart = afterIdx;
                  }
                }
                return false;
              })()`,
            }, { sessionId });

            // Wait for scroll and selection to settle
            await sleep(800);

            // Verify selection matches the placeholder
            const selectionCheck = await cdp!.send<{ result: { value: string } }>('Runtime.evaluate', {
              expression: `window.getSelection()?.toString() || ''`,
              returnByValue: true,
            }, { sessionId });

            const selectedText = selectionCheck.result.value.trim();
            if (selectedText === img.placeholder) {
              console.log(`[x-article] Selection verified: "${selectedText}"`);
              return true;
            }

            if (attempt < maxRetries) {
              console.log(`[x-article] Selection attempt ${attempt} got "${selectedText}", retrying...`);
              await sleep(500);
            } else {
              console.warn(`[x-article] Selection failed after ${maxRetries} attempts, got: "${selectedText}"`);
            }
          }
          return false;
        };

        // Try to select the placeholder
        const selected = await selectPlaceholder(3);
        if (!selected) {
          console.warn(`[x-article] Skipping image - could not select placeholder: ${img.placeholder}`);
          continue;
        }

        console.log(`[x-article] Copying image: ${path.basename(img.localPath)}`);

        // Copy image to clipboard
        if (!copyImageToClipboard(img.localPath)) {
          console.warn(`[x-article] Failed to copy image to clipboard`);
          continue;
        }

        // Wait for clipboard to be fully ready
        await sleep(1000);

        // Delete placeholder using execCommand (more reliable than keyboard events for DraftJS)
        console.log(`[x-article] Deleting placeholder...`);
        const deleteResult = await cdp.send<{ result: { value: boolean } }>('Runtime.evaluate', {
          expression: `(() => {
            const sel = window.getSelection();
            if (!sel || sel.isCollapsed) return false;
            // Try execCommand delete first
            if (document.execCommand('delete', false)) return true;
            // Fallback: replace selection with empty using insertText
            document.execCommand('insertText', false, '');
            return true;
          })()`,
          returnByValue: true,
        }, { sessionId });

        await sleep(500);

        // Check that placeholder is no longer in editor (exact match, not substring)
        const afterDelete = await cdp.send<{ result: { value: boolean } }>('Runtime.evaluate', {
          expression: `(() => {
            const editor = document.querySelector('.DraftEditor-editorContainer [data-contents="true"]');
            if (!editor) return true;
            const text = editor.innerText;
            const placeholder = ${JSON.stringify(img.placeholder)};
            // Use regex to find exact match (not followed by digit)
            const regex = new RegExp(placeholder + '(?!\\\\d)');
            return !regex.test(text);
          })()`,
          returnByValue: true,
        }, { sessionId });

        if (!afterDelete.result.value) {
          console.warn(`[x-article] Placeholder may not have been deleted, trying dispatchEvent...`);
          // Try selecting and deleting with InputEvent
          await selectPlaceholder(1);
          await sleep(300);
          await cdp.send('Runtime.evaluate', {
            expression: `(() => {
              const editor = document.querySelector('.DraftEditor-editorContainer [contenteditable="true"]');
              if (!editor) return;
              editor.focus();
              // Dispatch beforeinput and input events for deletion
              const beforeEvent = new InputEvent('beforeinput', { inputType: 'deleteContentBackward', bubbles: true, cancelable: true });
              editor.dispatchEvent(beforeEvent);
              const inputEvent = new InputEvent('input', { inputType: 'deleteContentBackward', bubbles: true });
              editor.dispatchEvent(inputEvent);
            })()`,
          }, { sessionId });
          await sleep(500);
        }

        // Count existing image blocks before paste
        const imgCountBefore = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
          expression: `document.querySelectorAll('section[data-block="true"][contenteditable="false"] img[src^="blob:"]').length`,
          returnByValue: true,
        }, { sessionId });

        // Focus editor to ensure cursor is in position
        await cdp.send('Runtime.evaluate', {
          expression: `(() => {
            const editor = document.querySelector('.DraftEditor-editorContainer [contenteditable="true"]');
            if (editor) editor.focus();
          })()`,
        }, { sessionId });
        await sleep(300);

        // Paste image using paste script (activates Chrome, sends real keystroke)
        console.log(`[x-article] Pasting image...`);
        if (pasteFromClipboard('Google Chrome', 5, 1000)) {
          console.log(`[x-article] Image pasted: ${path.basename(img.localPath)}`);
        } else {
          console.warn(`[x-article] Failed to paste image after retries`);
        }

        // Verify image appeared in editor
        console.log(`[x-article] Verifying image upload...`);
        const expectedImgCount = imgCountBefore.result.value + 1;
        let imgUploadOk = false;
        const imgWaitStart = Date.now();
        while (Date.now() - imgWaitStart < 15_000) {
          const r = await cdp!.send<{ result: { value: number } }>('Runtime.evaluate', {
            expression: `document.querySelectorAll('section[data-block="true"][contenteditable="false"] img[src^="blob:"]').length`,
            returnByValue: true,
          }, { sessionId });
          if (r.result.value >= expectedImgCount) {
            imgUploadOk = true;
            break;
          }
          await sleep(1000);
        }

        if (imgUploadOk) {
          console.log(`[x-article] Image upload verified (${expectedImgCount} image block(s))`);
          // Wait for DraftEditor DOM to stabilize after image insertion
          await sleep(3000);
        } else {
          console.warn(`[x-article] Image upload not detected after 15s`);
          if (i === 0) {
            console.error('[x-article] First image paste failed. Run check-paste-permissions.ts to diagnose.');
          }
        }
      }

      console.log('[x-article] All images processed.');

      // Final verification: check placeholder residue and image count
      console.log('[x-article] Running post-composition verification...');
      const finalEditorContent = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
        expression: `document.querySelector('.DraftEditor-editorContainer [data-contents="true"]')?.innerText || ''`,
        returnByValue: true,
      }, { sessionId });

      const remainingPlaceholders: string[] = [];
      for (const img of parsed.contentImages) {
        const regex = new RegExp(img.placeholder + '(?!\\d)');
        if (regex.test(finalEditorContent.result.value)) {
          remainingPlaceholders.push(img.placeholder);
        }
      }

      const finalImgCount = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
        expression: `document.querySelectorAll('section[data-block="true"][contenteditable="false"] img[src^="blob:"]').length`,
        returnByValue: true,
      }, { sessionId });

      const expectedCount = parsed.contentImages.length;
      const actualCount = finalImgCount.result.value;

      if (remainingPlaceholders.length > 0 || actualCount < expectedCount) {
        console.warn('[x-article] ⚠ POST-COMPOSITION CHECK FAILED:');
        if (remainingPlaceholders.length > 0) {
          console.warn(`[x-article]   Remaining placeholders: ${remainingPlaceholders.join(', ')}`);
        }
        if (actualCount < expectedCount) {
          console.warn(`[x-article]   Image count: expected ${expectedCount}, found ${actualCount}`);
        }
        console.warn('[x-article]   Please check the article before publishing.');
      } else {
        console.log(`[x-article] ✓ Verification passed: ${actualCount} image(s), no remaining placeholders.`);
      }
    }

    // Before preview: blur editor to trigger save
    console.log('[x-article] Triggering content save...');
    await cdp.send('Runtime.evaluate', {
      expression: `(() => {
        // Blur editor to trigger any pending saves
        const editor = document.querySelector('.DraftEditor-editorContainer [contenteditable="true"]');
        if (editor) {
          editor.blur();
        }
        // Also click elsewhere to ensure focus is lost
        document.body.click();
      })()`,
    }, { sessionId });
    await sleep(1500);

    // Click Preview button
    console.log('[x-article] Opening preview...');
    const previewSelectors = JSON.stringify(I18N_SELECTORS.previewButton);
    const previewClicked = await cdp.send<{ result: { value: boolean } }>('Runtime.evaluate', {
      expression: `(() => {
        const selectors = ${previewSelectors};
        for (const sel of selectors) {
          const el = document.querySelector(sel);
          if (el) { el.click(); return true; }
        }
        return false;
      })()`,
      returnByValue: true,
    }, { sessionId });

    if (previewClicked.result.value) {
      console.log('[x-article] Preview opened');
      await sleep(3000);
    } else {
      console.log('[x-article] Preview button not found');
    }

    // Check for publish button
    if (submit) {
      console.log('[x-article] Publishing...');
      const publishSelectors = JSON.stringify(I18N_SELECTORS.publishButton);
      await cdp.send('Runtime.evaluate', {
        expression: `(() => {
          const selectors = ${publishSelectors};
          for (const sel of selectors) {
            const el = document.querySelector(sel);
            if (el && !el.disabled) { el.click(); return true; }
          }
          return false;
        })()`,
      }, { sessionId });
      await sleep(3000);
      console.log('[x-article] Article published!');
    } else {
      console.log('[x-article] Article composed (draft mode).');
      console.log('[x-article] Browser remains open for manual review.');
    }

  } finally {
    // Disconnect CDP but keep browser open
    if (cdp) {
      cdp.close();
    }
    // Don't kill Chrome - let user review and close manually
  }
}

function printUsage(): never {
  console.log(`Publish Markdown article to X (Twitter) Articles

Usage:
  npx -y bun x-article.ts <markdown_file> [options]

Options:
  --title <title>     Override title
  --cover <image>     Override cover image
  --submit            Actually publish (default: draft only)
  --profile <dir>     Chrome profile directory
  --help              Show this help

Markdown frontmatter:
  ---
  title: My Article Title
  cover_image: /path/to/cover.jpg
  ---

Example:
  npx -y bun x-article.ts article.md
  npx -y bun x-article.ts article.md --cover ./hero.png
  npx -y bun x-article.ts article.md --submit
`);
  process.exit(0);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
  }

  let markdownPath: string | undefined;
  let title: string | undefined;
  let coverImage: string | undefined;
  let submit = false;
  let profileDir: string | undefined;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]!;
    if (arg === '--title' && args[i + 1]) {
      title = args[++i];
    } else if (arg === '--cover' && args[i + 1]) {
      const raw = args[++i]!;
      coverImage = path.isAbsolute(raw) ? raw : path.resolve(process.cwd(), raw);
    } else if (arg === '--submit') {
      submit = true;
    } else if (arg === '--profile' && args[i + 1]) {
      profileDir = args[++i];
    } else if (!arg.startsWith('-')) {
      markdownPath = arg;
    }
  }

  if (!markdownPath) {
    console.error('Error: Markdown file path required');
    process.exit(1);
  }

  if (!fs.existsSync(markdownPath)) {
    console.error(`Error: File not found: ${markdownPath}`);
    process.exit(1);
  }

  await publishArticle({ markdownPath, title, coverImage, submit, profileDir });
}

await main().catch((err) => {
  console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});
