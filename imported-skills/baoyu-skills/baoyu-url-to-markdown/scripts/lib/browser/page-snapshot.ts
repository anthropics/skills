import type { BrowserSession } from "./session";

export interface CapturedPageSnapshot {
  html: string;
  finalUrl: string;
}

export const CAPTURE_NORMALIZED_PAGE_SCRIPT = String.raw`
(() => {
  const baseUrl = document.baseURI || location.href;
  const htmlClone = document.documentElement.cloneNode(true);

  function materializeShadowDom(sourceRoot, cloneRoot) {
    const sourceElements = Array.from(sourceRoot.querySelectorAll("*"));
    const cloneElements = Array.from(cloneRoot.querySelectorAll("*"));

    for (let index = sourceElements.length - 1; index >= 0; index -= 1) {
      const sourceElement = sourceElements[index];
      const cloneElement = cloneElements[index];
      const shadowRoot = sourceElement && sourceElement.shadowRoot;
      if (!shadowRoot || !cloneElement || !shadowRoot.innerHTML) {
        continue;
      }

      if (cloneElement.tagName && cloneElement.tagName.includes("-")) {
        const wrapper = document.createElement("div");
        wrapper.setAttribute("data-shadow-host", cloneElement.tagName.toLowerCase());
        wrapper.innerHTML = shadowRoot.innerHTML;
        cloneElement.replaceWith(wrapper);
      } else {
        cloneElement.innerHTML = shadowRoot.innerHTML;
      }
    }
  }

  function toAbsolute(url) {
    if (!url) return url;
    try {
      return new URL(url, baseUrl).href;
    } catch {
      return url;
    }
  }

  function absolutizeAttribute(root, selector, attribute) {
    root.querySelectorAll(selector).forEach((element) => {
      const value = element.getAttribute(attribute);
      if (!value) return;
      const absolute = toAbsolute(value);
      if (absolute) {
        element.setAttribute(attribute, absolute);
      }
    });
  }

  function absolutizeSrcset(root, selector) {
    root.querySelectorAll(selector).forEach((element) => {
      const srcset = element.getAttribute("srcset");
      if (!srcset) return;
      element.setAttribute(
        "srcset",
        srcset
          .split(",")
          .map((part) => {
            const trimmed = part.trim();
            if (!trimmed) return "";
            const [url, ...descriptor] = trimmed.split(/\s+/);
            const absolute = toAbsolute(url);
            return descriptor.length > 0 ? absolute + " " + descriptor.join(" ") : absolute;
          })
          .filter(Boolean)
          .join(", "),
      );
    });
  }

  materializeShadowDom(document.documentElement, htmlClone);

  htmlClone
    .querySelectorAll("img[data-src], video[data-src], audio[data-src], source[data-src]")
    .forEach((element) => {
      const dataSource = element.getAttribute("data-src");
      const current = element.getAttribute("src");
      if (dataSource && (!current || current === "" || current.startsWith("data:"))) {
        element.setAttribute("src", dataSource);
      }
    });

  absolutizeAttribute(htmlClone, "a[href]", "href");
  absolutizeAttribute(htmlClone, "img[src], video[src], audio[src], source[src], iframe[src]", "src");
  absolutizeAttribute(htmlClone, "video[poster]", "poster");
  absolutizeSrcset(htmlClone, "img[srcset], source[srcset]");

  return {
    html: "<!doctype html>\n" + htmlClone.outerHTML,
    finalUrl: location.href,
  };
})()
`;

export async function captureNormalizedPageSnapshot(
  browser: BrowserSession,
): Promise<CapturedPageSnapshot> {
  return browser.evaluate<CapturedPageSnapshot>(CAPTURE_NORMALIZED_PAGE_SCRIPT);
}
