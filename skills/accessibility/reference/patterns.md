# Accessibility Patterns

Copy-paste ready implementations for common accessibility needs.

## Skip Links

The first focusable element on every page. Lets keyboard and switch users bypass repeated navigation.

```html
<!-- Place immediately after <body> -->
<a href="#main-content" class="skip-link">Skip to main content</a>

<header>
  <nav aria-label="Primary navigation">
    <!-- navigation links -->
  </nav>
</header>

<main id="main-content" tabindex="-1">
  <!-- page content -->
</main>
```

Enhanced focus behavior (ensures all browsers move focus correctly):

```js
document.querySelectorAll('.skip-link').forEach(link => {
  link.addEventListener('click', function(e) {
    const targetId = this.getAttribute('href').substring(1);
    const target = document.getElementById(targetId);
    if (target) {
      e.preventDefault();
      if (!target.hasAttribute('tabindex')) {
        target.setAttribute('tabindex', '-1');
      }
      target.focus();
      target.scrollIntoView({ behavior: 'smooth', block: 'start' });
    }
  });
});
```

---

## Landmark Structure

Screen readers navigate by landmarks. Use semantic HTML5 elements with `aria-label` to differentiate multiples.

```html
<header role="banner">
  <nav role="navigation" aria-label="Primary navigation">...</nav>
</header>

<main role="main" id="main-content" tabindex="-1">
  <h1>Page Title</h1>
  <section>
    <h2>Section Heading</h2>
    <!-- content -->
  </section>
  <nav aria-label="Section navigation">...</nav>
</main>

<aside role="complementary" aria-label="Related resources">...</aside>

<footer role="contentinfo">
  <nav aria-label="Footer navigation">...</nav>
</footer>
```

Rules:
- One `<main>` per page
- One `<header role="banner">` per page (unless inside `<article>`)
- Use `aria-label` when you have multiple `<nav>` elements
- `tabindex="-1"` on skip link targets so they can receive focus

---

## Focus Trap

Trap focus inside modal dialogs. Tab cycles through the modal's focusable elements. Escape closes. Focus restores to the trigger element on close.

```js
class FocusTrap {
  constructor(element) {
    this.element = element;
    this.focusableSelector =
      'a[href], button:not([disabled]), textarea:not([disabled]), ' +
      'input:not([disabled]), select:not([disabled]), [tabindex]:not([tabindex="-1"])';
    this.previousFocus = null;
  }

  activate() {
    this.previousFocus = document.activeElement;
    const focusable = Array.from(
      this.element.querySelectorAll(this.focusableSelector)
    );
    if (focusable.length > 0) {
      focusable[0].focus();
    }
    this.element.addEventListener('keydown', this._handleKeydown);
  }

  deactivate() {
    this.element.removeEventListener('keydown', this._handleKeydown);
    if (this.previousFocus && this.previousFocus.focus) {
      this.previousFocus.focus();
    }
  }

  _handleKeydown = (e) => {
    if (e.key !== 'Tab') return;

    const focusable = Array.from(
      this.element.querySelectorAll(this.focusableSelector)
    );
    const first = focusable[0];
    const last = focusable[focusable.length - 1];

    if (e.shiftKey && document.activeElement === first) {
      e.preventDefault();
      last.focus();
    } else if (!e.shiftKey && document.activeElement === last) {
      e.preventDefault();
      first.focus();
    }
  };
}

// Usage:
// const trap = new FocusTrap(document.getElementById('modal'));
// trap.activate();   // on open
// trap.deactivate();  // on close
```

---

## Roving Tabindex

For composite widgets like tab lists, toolbars, and menus. One element is tabbable (tabindex="0"), the rest are tabindex="-1". Arrow keys move focus within the group.

```js
class RovingTabindex {
  constructor(container, itemSelector, orientation = 'horizontal') {
    this.container = container;
    this.items = Array.from(container.querySelectorAll(itemSelector));
    this.orientation = orientation;
    this.currentIndex = 0;

    // Set initial state
    this.items.forEach((item, i) => {
      item.setAttribute('tabindex', i === 0 ? '0' : '-1');
    });

    container.addEventListener('keydown', (e) => this._handleKeydown(e));
  }

  _handleKeydown(e) {
    const prev = this.orientation === 'horizontal' ? 'ArrowLeft' : 'ArrowUp';
    const next = this.orientation === 'horizontal' ? 'ArrowRight' : 'ArrowDown';
    let newIndex = this.currentIndex;

    switch (e.key) {
      case next:
        e.preventDefault();
        newIndex = (this.currentIndex + 1) % this.items.length;
        break;
      case prev:
        e.preventDefault();
        newIndex = (this.currentIndex - 1 + this.items.length) % this.items.length;
        break;
      case 'Home':
        e.preventDefault();
        newIndex = 0;
        break;
      case 'End':
        e.preventDefault();
        newIndex = this.items.length - 1;
        break;
      default:
        return;
    }

    this.items[this.currentIndex].setAttribute('tabindex', '-1');
    this.items[newIndex].setAttribute('tabindex', '0');
    this.items[newIndex].focus();
    this.currentIndex = newIndex;
  }
}

// Usage:
// new RovingTabindex(
//   document.querySelector('[role="tablist"]'),
//   '[role="tab"]',
//   'horizontal'
// );
```

---

## Screen Reader Announcements

Announce dynamic content changes to screen readers via ARIA live regions.

```js
/**
 * Announce a message to screen readers.
 * @param {string} message - What to announce
 * @param {'polite'|'assertive'} priority - polite waits for pause, assertive interrupts
 *
 * When to use each:
 *   polite: Form saved, search results count, theme changed, item added to cart
 *   assertive: Validation errors, session timeout warnings, connection lost
 *
 * Important: Live regions must exist in the DOM BEFORE content is injected.
 * This function handles that by creating the element first, then setting text
 * after a microtask.
 */
function announce(message, priority = 'polite') {
  const el = document.createElement('div');
  el.setAttribute('role', 'status');
  el.setAttribute('aria-live', priority);
  el.setAttribute('aria-atomic', 'true');
  el.className = 'sr-only';
  document.body.appendChild(el);
  // Delay setting text so the live region is registered before populated
  requestAnimationFrame(() => {
    el.textContent = message;
  });
  setTimeout(() => el.remove(), 1000);
}

// Common patterns:
announce('Form submitted successfully');
announce('Error: email is required', 'assertive');
announce(`${count} results found for "${query}"`);
announce('Page loaded: Settings');
announce('Theme changed to High Contrast');
announce(`Showing ${visible} of ${total} items`);
```

For frequent updates (chat, live data), use a persistent live region instead of creating/destroying elements:

```js
// Create once
const liveRegion = document.createElement('div');
liveRegion.id = 'live-updates';
liveRegion.setAttribute('role', 'status');
liveRegion.setAttribute('aria-live', 'polite');
liveRegion.className = 'sr-only';
document.body.appendChild(liveRegion);

// Update as needed
liveRegion.textContent = `New message from ${username}`;
```

---

## Accessible Modal Dialog

### Preferred: Native `<dialog>` Element

The native `<dialog>` element with `showModal()` is the best approach for modern browsers. It handles focus trapping, Escape key, backdrop, and `aria-modal` automatically — no JavaScript focus management needed.

```html
<dialog id="modal" aria-labelledby="modal-title">
  <h2 id="modal-title">Dialog Title</h2>
  <div>
    <!-- modal content -->
  </div>
  <button id="modal-close" aria-label="Close dialog">Close</button>
</dialog>
```

```js
const dialog = document.getElementById('modal');
const trigger = document.querySelector('[data-opens="modal"]');

// Open
trigger.addEventListener('click', () => {
  dialog.showModal(); // Focus traps automatically, adds backdrop
});

// Close via button
dialog.querySelector('#modal-close').addEventListener('click', () => {
  dialog.close(); // Focus returns to trigger automatically
});

// Close via backdrop click
dialog.addEventListener('click', (e) => {
  if (e.target === dialog) dialog.close();
});
```

```css
/* Style the backdrop */
dialog::backdrop {
  background: rgba(0, 0, 0, 0.5);
}
```

### Fallback: Custom Modal with Focus Trap

For browsers that don't support `<dialog>`, or when you need custom behavior. Uses the FocusTrap class from above.

```html
<div id="modal" role="dialog" aria-modal="true" aria-labelledby="modal-title" hidden>
  <h2 id="modal-title">Dialog Title</h2>
  <div>
    <!-- modal content -->
  </div>
  <button id="modal-close" aria-label="Close dialog">Close</button>
</div>
```

```js
function openModal(modalEl, triggerEl) {
  modalEl.hidden = false;
  modalEl.setAttribute('aria-hidden', 'false');

  // Mark background content as inert (preferred over aria-hidden on siblings)
  document.querySelector('main')?.setAttribute('inert', '');

  const trap = new FocusTrap(modalEl);
  trap.activate();

  const handleEscape = (e) => {
    if (e.key === 'Escape') closeModal(modalEl, triggerEl, trap, handleEscape);
  };
  document.addEventListener('keydown', handleEscape);

  modalEl._trap = trap;
  modalEl._escapeHandler = handleEscape;

  announce('Dialog opened: ' + modalEl.querySelector('[id$="-title"]')?.textContent);
}

function closeModal(modalEl, triggerEl, trap, escapeHandler) {
  modalEl.hidden = true;
  modalEl.setAttribute('aria-hidden', 'true');

  document.querySelector('main')?.removeAttribute('inert');

  trap = trap || modalEl._trap;
  escapeHandler = escapeHandler || modalEl._escapeHandler;

  if (trap) trap.deactivate();
  if (escapeHandler) document.removeEventListener('keydown', escapeHandler);
  if (triggerEl) triggerEl.focus();

  announce('Dialog closed');
}
```

---

## Accessible Theme Switcher

Toggle between themes with screen reader announcements, localStorage persistence, and OS preference detection.

```js
function initThemeSwitcher(storageKey = 'theme', defaultTheme = 'light') {
  const saved = localStorage.getItem(storageKey) || defaultTheme;
  applyTheme(saved);

  document.querySelectorAll('[data-theme-toggle]').forEach(btn => {
    const theme = btn.dataset.themeToggle;
    btn.setAttribute('aria-pressed', theme === saved ? 'true' : 'false');

    btn.addEventListener('click', () => {
      applyTheme(theme);
      localStorage.setItem(storageKey, theme);

      // Update button states
      document.querySelectorAll('[data-theme-toggle]').forEach(b => {
        b.setAttribute('aria-pressed', b.dataset.themeToggle === theme ? 'true' : 'false');
      });

      announce(`Theme changed to ${btn.textContent.trim()}`);
    });
  });
}

function applyTheme(theme) {
  document.documentElement.setAttribute('data-theme', theme);
}
```

Suggested theme presets for accessibility:

```css
/* High contrast dark (default accessible) */
[data-theme="dark"] {
  --bg: #000000;
  --text: #ffffff;
  --accent: #58a6ff;
  --focus-ring: #ffff00;
}

/* CVI-optimized (Cortical Visual Impairment) */
[data-theme="cvi"] {
  --bg: #000000;
  --text: #ffff00;
  --accent: #ffff00;
  --focus-ring: #00ffff;
}

/* Low-light / photophobia friendly */
[data-theme="low-light"] {
  --bg: #0d1117;
  --text: #8b949e;
  --accent: #4a6fa5;
  --focus-ring: #6a9bcc;
}

/* Deuteranopia-friendly (red-green color blindness) */
[data-theme="deuteranopia"] {
  --bg: #1a1a1a;
  --text: #e0e0e0;
  --accent: #ff8c00; /* orange instead of green */
  --focus-ring: #ffff00;
}
```
