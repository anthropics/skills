import type { AdapterContext } from "../types";
import { extractThreadTweetsFromPayloads } from "./thread";
import { collectXJsonPayloads, getRelevantXThreadEntries, prefetchRelevantXThreadBodies } from "./payloads";

interface ClickTextResult {
  clicked: boolean;
  text?: string;
}

interface ScrollStepResult {
  moved: boolean;
  atTop: boolean;
  atBottom: boolean;
}

interface ThreadProgress {
  tweetCount: number;
  firstTweetId?: string;
  lastTweetId?: string;
  requestCount: number;
  tweetDetailCount: number;
}

interface TopProbeState {
  requestCount: number;
  tweetDetailCount: number;
  scrollHeight: number;
}

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function waitForXNetworkSettle(context: AdapterContext, reason: string): Promise<void> {
  try {
    await context.network.waitForIdle({
      idleMs: 650,
      timeoutMs: Math.min(context.timeoutMs, 5_000),
    });
  } catch {
    context.log.debug(`Network idle timed out after ${reason}.`);
  }
}

async function captureTopProbeState(context: AdapterContext): Promise<TopProbeState> {
  const entries = getRelevantXThreadEntries(context);
  const scrollHeight = await context.browser.evaluate<number>(`
    (() => {
      const scrollRoot = document.scrollingElement ?? document.documentElement ?? document.body;
      return scrollRoot.scrollHeight;
    })()
  `);

  return {
    requestCount: entries.length,
    tweetDetailCount: entries.filter((entry) => entry.url.includes("TweetDetail")).length,
    scrollHeight,
  };
}

async function waitForTopProbe(context: AdapterContext): Promise<boolean> {
  const initial = await captureTopProbeState(context);
  const deadline = Date.now() + 1_200;

  while (Date.now() < deadline) {
    try {
      await context.network.waitForIdle({
        idleMs: 250,
        timeoutMs: 350,
      });
    } catch {
      // Keep polling until the shorter top-probe budget expires.
    }

    await prefetchRelevantXThreadBodies(context);
    const next = await captureTopProbeState(context);
    if (
      next.requestCount > initial.requestCount ||
      next.tweetDetailCount > initial.tweetDetailCount ||
      next.scrollHeight > initial.scrollHeight + 4
    ) {
      context.log.debug("Observed additional X thread activity while probing the page top.");
      return true;
    }

    await sleep(120);
  }

  return false;
}

async function scrollThreadToTop(context: AdapterContext): Promise<void> {
  let settledTopChecks = 0;

  while (settledTopChecks < 2) {
    const scroll = await context.browser.evaluate<ScrollStepResult>(`
      (() => {
        const scrollRoot = document.scrollingElement ?? document.documentElement ?? document.body;
        const before = window.scrollY;
        window.scrollTo({ top: 0, left: 0, behavior: "instant" });
        const after = window.scrollY;
        return {
          moved: after !== before,
          atTop: after <= 4,
          atBottom: window.innerHeight + after >= scrollRoot.scrollHeight - 4,
        };
      })()
    `);
    await sleep(140);
    await waitForXNetworkSettle(context, "scrolling X thread to top");
    await prefetchRelevantXThreadBodies(context);

    if (scroll.moved) {
      settledTopChecks = 0;
      continue;
    }

    const observedTopActivity = await waitForTopProbe(context);
    if (observedTopActivity) {
      settledTopChecks = 0;
      continue;
    }

    settledTopChecks += 1;
  }
}

async function clickVisibleShowReplies(context: AdapterContext): Promise<ClickTextResult> {
  return context.browser.evaluate<ClickTextResult>(`
    (() => {
      const normalize = (value) => value.replace(/\\s+/g, " ").trim();
      const matches = [
        /^Show replies$/i,
        /^Show more replies$/i,
        /^Show additional replies$/i,
        /^显示回复$/,
        /^展开回复$/,
      ];
      const isVisible = (element) => {
        if (!(element instanceof HTMLElement)) {
          return false;
        }
        const rect = element.getBoundingClientRect();
        const style = window.getComputedStyle(element);
        return (
          rect.width > 0 &&
          rect.height > 0 &&
          style.visibility !== "hidden" &&
          style.display !== "none"
        );
      };

      const selectors = [
        "a",
        "button",
        '[role="button"]',
        '[role="link"]',
      ];

      for (const element of document.querySelectorAll(selectors.join(","))) {
        if (!isVisible(element)) {
          continue;
        }
        const text = normalize(element.textContent ?? "");
        if (!text || !matches.some((pattern) => pattern.test(text))) {
          continue;
        }
        element.scrollIntoView({ block: "center", inline: "nearest" });
        if (element instanceof HTMLElement) {
          element.click();
          return { clicked: true, text };
        }
      }

      return { clicked: false };
    })()
  `);
}

async function expandVisibleShowReplies(context: AdapterContext): Promise<number> {
  let clickCount = 0;

  while (clickCount < 8) {
    const result = await clickVisibleShowReplies(context).catch<ClickTextResult>(() => ({ clicked: false }));
    if (!result.clicked) {
      break;
    }

    clickCount += 1;
    context.log.debug(`Expanded X thread replies via "${result.text ?? "Show replies"}".`);
    await sleep(250);
    await waitForXNetworkSettle(context, "expanding Show replies");
    await prefetchRelevantXThreadBodies(context);
  }

  return clickCount;
}

async function scrollThreadBy(context: AdapterContext, stepPx: number): Promise<ScrollStepResult> {
  const result = await context.browser.evaluate<ScrollStepResult>(`
    (() => {
      const scrollRoot = document.scrollingElement ?? document.documentElement ?? document.body;
      const before = window.scrollY;
      window.scrollBy({ top: ${stepPx}, left: 0, behavior: "instant" });
      const after = window.scrollY;
      return {
        moved: after !== before,
        atTop: after <= 4,
        atBottom: window.innerHeight + after >= scrollRoot.scrollHeight - 4,
      };
    })()
  `);

  await sleep(140);
  await waitForXNetworkSettle(context, "scrolling X thread");
  await prefetchRelevantXThreadBodies(context);
  return result;
}

async function captureThreadProgress(context: AdapterContext, statusId: string): Promise<ThreadProgress> {
  const entries = getRelevantXThreadEntries(context);
  const payloads = await collectXJsonPayloads(context);
  const tweets = extractThreadTweetsFromPayloads(payloads, statusId, context.input.url.toString());
  return {
    tweetCount: tweets.length,
    firstTweetId: tweets[0]?.id,
    lastTweetId: tweets[tweets.length - 1]?.id,
    requestCount: entries.length,
    tweetDetailCount: entries.filter((entry) => entry.url.includes("TweetDetail")).length,
  };
}

export async function loadFullXThread(context: AdapterContext, statusId: string): Promise<void> {
  await scrollThreadToTop(context);

  let progress = await captureThreadProgress(context, statusId);
  let stagnantRounds = 0;
  let roundsWithoutMovement = 0;
  let distanceWithoutThreadActivityPx = 0;

  for (let round = 0; ; round += 1) {
    const stepPx = round < 12 ? 1_200 : 1_600;
    let expandedCount = await expandVisibleShowReplies(context);
    const scroll = await scrollThreadBy(context, stepPx);
    expandedCount += await expandVisibleShowReplies(context);
    const nextProgress = await captureThreadProgress(context, statusId);
    const grew =
      nextProgress.tweetCount > progress.tweetCount ||
      nextProgress.firstTweetId !== progress.firstTweetId ||
      nextProgress.lastTweetId !== progress.lastTweetId ||
      nextProgress.requestCount > progress.requestCount ||
      nextProgress.tweetDetailCount > progress.tweetDetailCount;

    if (grew) {
      context.log.debug(
        `X thread progress: ${nextProgress.tweetCount} tweets (${nextProgress.firstTweetId ?? "unknown"} -> ${nextProgress.lastTweetId ?? "unknown"}), ${nextProgress.requestCount} requests, ${nextProgress.tweetDetailCount} TweetDetail.`,
      );
      stagnantRounds = 0;
      distanceWithoutThreadActivityPx = 0;
    } else if (expandedCount > 0) {
      stagnantRounds = 0;
      distanceWithoutThreadActivityPx = 0;
    } else {
      stagnantRounds += 1;
      distanceWithoutThreadActivityPx += stepPx;
    }

    roundsWithoutMovement = scroll.moved ? 0 : roundsWithoutMovement + 1;
    progress = nextProgress;

    if (scroll.atBottom && stagnantRounds >= 6) {
      context.log.debug("Stopping X thread scroll after reaching page bottom with no further thread progress.");
      break;
    }

    if (roundsWithoutMovement >= 2 && stagnantRounds >= 4) {
      context.log.debug("Stopping X thread scroll after repeated downward scrolls no longer move the page.");
      break;
    }

    if (distanceWithoutThreadActivityPx >= 24_000 && stagnantRounds >= 12) {
      context.log.debug("Stopping X thread scroll after a long stretch with no thread-related progress.");
      break;
    }
  }
}
