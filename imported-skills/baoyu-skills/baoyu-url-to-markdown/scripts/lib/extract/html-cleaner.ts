import { JSDOM } from "jsdom";

export interface CleanHtmlOptions {
  removeAds?: boolean;
  removeBase64Images?: boolean;
  onlyMainContent?: boolean;
  includeSelectors?: string[];
  excludeSelectors?: string[];
}

const ALWAYS_REMOVE_SELECTORS = [
  "script",
  "style",
  "noscript",
  "link[rel='stylesheet']",
  "[hidden]",
  "[aria-hidden='true']",
  "[style*='display: none']",
  "[style*='display:none']",
  "[style*='visibility: hidden']",
  "[style*='visibility:hidden']",
  "svg[aria-hidden='true']",
  "svg.icon",
  "svg[class*='icon']",
  "template",
  "meta",
  "iframe",
  "canvas",
  "object",
  "embed",
  "form",
  "input",
  "select",
  "textarea",
  "button",
];

const OVERLAY_SELECTORS = [
  "[class*='modal']",
  "[class*='popup']",
  "[class*='overlay']",
  "[class*='dialog']",
  "[role='dialog']",
  "[role='alertdialog']",
  "[class*='cookie']",
  "[class*='consent']",
  "[class*='gdpr']",
  "[class*='privacy-banner']",
  "[class*='notification-bar']",
  "[id*='cookie']",
  "[id*='consent']",
  "[id*='gdpr']",
  "[style*='position: fixed']",
  "[style*='position:fixed']",
  "[style*='position: sticky']",
  "[style*='position:sticky']",
];

const NAVIGATION_SELECTORS = [
  "header",
  "footer",
  "nav",
  "aside",
  ".header",
  ".top",
  ".navbar",
  "#header",
  ".footer",
  ".bottom",
  "#footer",
  ".sidebar",
  ".side",
  ".aside",
  "#sidebar",
  ".modal",
  ".popup",
  "#modal",
  ".overlay",
  ".ad",
  ".ads",
  ".advert",
  "#ad",
  ".lang-selector",
  ".language",
  "#language-selector",
  ".social",
  ".social-media",
  ".social-links",
  "#social",
  ".menu",
  ".navigation",
  "#nav",
  ".breadcrumbs",
  "#breadcrumbs",
  ".share",
  "#share",
  ".widget",
  "#widget",
  ".cookie",
  "#cookie",
];

const FORCE_INCLUDE_SELECTORS = [
  "#main",
  "#content",
  "#main-content",
  "#article",
  "#post",
  "#page-content",
  "main",
  "article",
  "[role='main']",
  ".main-content",
  ".content",
  ".post-content",
  ".article-content",
  ".entry-content",
  ".page-content",
  ".article-body",
  ".post-body",
  ".story-content",
  ".blog-content",
];

const AD_SELECTORS = [
  "ins.adsbygoogle",
  ".google-ad",
  ".adsense",
  "[data-ad]",
  "[data-ads]",
  "[data-ad-slot]",
  "[data-ad-client]",
  ".ad-container",
  ".ad-wrapper",
  ".advertisement",
  ".sponsored-content",
  "img[width='1'][height='1']",
  "img[src*='pixel']",
  "img[src*='tracking']",
  "img[src*='analytics']",
];

function getLinkDensity(element: Element): number {
  const text = element.textContent || "";
  const textLength = text.trim().length;
  if (textLength === 0) {
    return 1;
  }

  let linkLength = 0;
  element.querySelectorAll("a").forEach((link) => {
    linkLength += (link.textContent || "").trim().length;
  });

  return linkLength / textLength;
}

function getContentScore(element: Element): number {
  let score = 0;
  const text = element.textContent || "";
  const textLength = text.trim().length;

  score += Math.min(textLength / 100, 50);
  score += element.querySelectorAll("p").length * 3;
  score += element.querySelectorAll("h1, h2, h3, h4, h5, h6").length * 2;
  score += element.querySelectorAll("img").length;

  score -= element.querySelectorAll("a").length * 0.5;
  score -= element.querySelectorAll("li").length * 0.2;

  const linkDensity = getLinkDensity(element);
  if (linkDensity > 0.5) {
    score -= 30;
  } else if (linkDensity > 0.3) {
    score -= 15;
  }

  const className = typeof element.className === "string" ? element.className : "";
  const classAndId = `${className} ${element.id || ""}`;
  if (/article|content|post|body|main|entry/i.test(classAndId)) {
    score += 25;
  }
  if (/comment|sidebar|footer|nav|menu|header|widget|ad/i.test(classAndId)) {
    score -= 25;
  }

  return score;
}

function looksLikeNavigation(element: Element): boolean {
  const linkDensity = getLinkDensity(element);
  if (linkDensity > 0.5) {
    return true;
  }

  const listItems = element.querySelectorAll("li");
  const links = element.querySelectorAll("a");
  return listItems.length > 5 && links.length > listItems.length * 0.8;
}

function removeElements(document: Document, selectors: string[]): void {
  for (const selector of selectors) {
    try {
      document.querySelectorAll(selector).forEach((element) => element.remove());
    } catch {
      // Ignore unsupported selectors.
    }
  }
}

function removeWithProtection(
  document: Document,
  selectorsToRemove: string[],
  protectedSelectors: string[],
): void {
  for (const selector of selectorsToRemove) {
    try {
      document.querySelectorAll(selector).forEach((element) => {
        const isProtected = protectedSelectors.some((protectedSelector) => {
          try {
            return element.matches(protectedSelector);
          } catch {
            return false;
          }
        });

        if (isProtected) {
          return;
        }

        const containsProtected = protectedSelectors.some((protectedSelector) => {
          try {
            return element.querySelector(protectedSelector) !== null;
          } catch {
            return false;
          }
        });

        if (containsProtected) {
          return;
        }

        element.remove();
      });
    } catch {
      // Ignore unsupported selectors.
    }
  }
}

function isValidContent(element: Element | null): element is Element {
  if (!element) {
    return false;
  }
  const text = element.textContent || "";
  if (text.trim().length < 100) {
    return false;
  }
  return !looksLikeNavigation(element);
}

function findMainContent(document: Document): Element | null {
  const main = document.querySelector("main");
  if (isValidContent(main) && getLinkDensity(main) < 0.4) {
    return main;
  }

  const roleMain = document.querySelector('[role="main"]');
  if (isValidContent(roleMain) && getLinkDensity(roleMain) < 0.4) {
    return roleMain;
  }

  const articles = document.querySelectorAll("article");
  if (articles.length === 1 && isValidContent(articles[0] ?? null)) {
    return articles[0] ?? null;
  }

  const contentSelectors = [
    "#content",
    "#main-content",
    "#main",
    ".content",
    ".main-content",
    ".post-content",
    ".article-content",
    ".entry-content",
    ".page-content",
    ".article-body",
    ".post-body",
    ".story-content",
    ".blog-content",
  ];

  for (const selector of contentSelectors) {
    try {
      const element = document.querySelector(selector);
      if (isValidContent(element) && getLinkDensity(element) < 0.4) {
        return element;
      }
    } catch {
      // Ignore invalid selectors.
    }
  }

  const candidates: Array<{ element: Element; score: number }> = [];
  document.querySelectorAll("div, section, article").forEach((element) => {
    const text = element.textContent || "";
    if (text.trim().length < 200) {
      return;
    }

    const score = getContentScore(element);
    if (score > 0) {
      candidates.push({ element, score });
    }
  });

  candidates.sort((left, right) => right.score - left.score);
  if ((candidates[0]?.score ?? 0) > 20) {
    return candidates[0]?.element ?? null;
  }

  return null;
}

function removeBase64ImagesFromDocument(document: Document): void {
  document.querySelectorAll("img[src^='data:']").forEach((element) => element.remove());

  document.querySelectorAll("[style*='data:image']").forEach((element) => {
    const style = element.getAttribute("style");
    if (!style) {
      return;
    }

    const cleanedStyle = style.replace(
      /background(-image)?:\s*url\([^)]*data:image[^)]*\)[^;]*;?/gi,
      "",
    );

    if (cleanedStyle.trim()) {
      element.setAttribute("style", cleanedStyle);
    } else {
      element.removeAttribute("style");
    }
  });

  document
    .querySelectorAll("source[src^='data:'], source[srcset*='data:']")
    .forEach((element) => element.remove());
}

function makeAbsoluteUrl(value: string, baseUrl: string): string | null {
  try {
    return new URL(value, baseUrl).toString();
  } catch {
    return null;
  }
}

function convertRelativeUrls(document: Document, baseUrl: string): void {
  document.querySelectorAll("[src]").forEach((element) => {
    const src = element.getAttribute("src");
    if (!src || src.startsWith("http") || src.startsWith("//") || src.startsWith("data:")) {
      return;
    }

    const absolute = makeAbsoluteUrl(src, baseUrl);
    if (absolute) {
      element.setAttribute("src", absolute);
    }
  });

  document.querySelectorAll("[href]").forEach((element) => {
    const href = element.getAttribute("href");
    if (
      !href ||
      href.startsWith("http") ||
      href.startsWith("//") ||
      href.startsWith("#") ||
      href.startsWith("mailto:") ||
      href.startsWith("tel:") ||
      href.startsWith("javascript:")
    ) {
      return;
    }

    const absolute = makeAbsoluteUrl(href, baseUrl);
    if (absolute) {
      element.setAttribute("href", absolute);
    }
  });
}

function removeComments(document: Document): void {
  const walker = document.createTreeWalker(document, document.defaultView?.NodeFilter.SHOW_COMMENT ?? 128);
  const comments: Comment[] = [];
  while (walker.nextNode()) {
    comments.push(walker.currentNode as Comment);
  }
  comments.forEach((comment) => comment.parentNode?.removeChild(comment));
}

export function cleanHtml(
  html: string,
  baseUrl: string,
  options: CleanHtmlOptions = {},
): string {
  const {
    removeAds = true,
    removeBase64Images = true,
    onlyMainContent = true,
    includeSelectors,
    excludeSelectors,
  } = options;

  const dom = new JSDOM(html, { url: baseUrl });
  const { document } = dom.window;

  removeElements(document, ALWAYS_REMOVE_SELECTORS);
  removeElements(document, OVERLAY_SELECTORS);

  if (removeAds) {
    removeElements(document, AD_SELECTORS);
  }

  if (excludeSelectors?.length) {
    removeElements(document, excludeSelectors);
  }

  if (onlyMainContent) {
    removeWithProtection(document, NAVIGATION_SELECTORS, FORCE_INCLUDE_SELECTORS);

    const mainContent = findMainContent(document);
    if (mainContent && document.body) {
      const clone = mainContent.cloneNode(true);
      document.body.innerHTML = "";
      document.body.appendChild(clone);
    }
  }

  if (includeSelectors?.length && document.body) {
    const matchedElements: Element[] = [];
    for (const selector of includeSelectors) {
      try {
        document.querySelectorAll(selector).forEach((element) => {
          matchedElements.push(element.cloneNode(true) as Element);
        });
      } catch {
        // Ignore invalid selectors.
      }
    }

    if (matchedElements.length > 0) {
      document.body.innerHTML = "";
      matchedElements.forEach((element) => document.body?.appendChild(element));
    }
  }

  if (removeBase64Images) {
    removeBase64ImagesFromDocument(document);
  }

  removeComments(document);
  convertRelativeUrls(document, baseUrl);

  return document.documentElement.outerHTML || html;
}
