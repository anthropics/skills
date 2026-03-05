# Navigation Patterns Reference

Navigation is how users find their way through a product. Poor navigation is the single biggest cause of user confusion — not bad visual design, not slow performance, but not knowing where you are or how to get somewhere.

---

## The Core Navigation Question

At any moment in the product, a user should be able to answer three questions instantly:
1. **Where am I?** — Current location is clearly indicated
2. **Where can I go?** — Available destinations are visible
3. **How do I get back?** — Return path is clear

If any of these fail, the navigation is broken.

---

## Navigation Types

### Primary Navigation
The main way to move between top-level sections of the product.

| Pattern | Use When | Platform |
|---|---|---|
| **Top nav bar** | 3–7 primary destinations | Desktop |
| **Side nav / sidebar** | 5–10 destinations, hierarchical | Desktop SaaS/tools |
| **Bottom nav bar** | 3–5 primary destinations | Mobile |
| **Hamburger menu** | Secondary items, overflow | Mobile (not primary) |
| **Tab bar** | Switching views of same context | Both |

### Secondary Navigation
Deeper levels within a section.

| Pattern | Use When |
|---|---|
| **Tabs** | Parallel views of same content (not different sections) |
| **Breadcrumbs** | 3+ levels deep in hierarchy |
| **Sidebar sub-nav** | Multi-level sections in desktop apps |
| **Segmented control** | 2–4 closely related views |

---

## Active States

The currently active nav item must be **unambiguously distinct** from inactive items.

### What Works
- **Filled background** on active item (most common, clearest)
- **Bottom border indicator** (tab bar pattern)
- **Left border indicator** (sidebar pattern)
- **Bold weight** on active label
- **Different color** for active icon + label

### What Doesn't Work
- Slightly different shade of the same color (too subtle)
- Color alone with no weight/position change (fails for colorblind users)
- Only the icon changes, not the label (too easy to miss)

### Contrast Requirement
Active nav item must have at least **3:1 contrast** against inactive items — not just visually "different."

### Code Pattern
```css
.nav-item { color: #6b7280; }
.nav-item.active {
  color: #111827;
  font-weight: 600;
  background: #f3f4f6;
  border-left: 3px solid #7c3aed; /* sidebar indicator */
}
```

---

## Tabs

Tabs switch between **parallel views of the same content or context**. They are NOT for top-level navigation between different sections.

### ✅ Correct Tab Usage
- Profile page: Overview | Activity | Settings
- Message thread: Messages | Files | Members
- Dashboard: Daily | Weekly | Monthly

### ❌ Incorrect Tab Usage
- Home | Projects | Settings | Help (these are different sections — use nav)
- Step 1 | Step 2 | Step 3 (these are sequential — use a stepper)

### Tab Rules
- **Tabs should be equal weight.** If one tab is visited 90% of the time, reconsider whether tabs are the right pattern.
- **Always show the active tab clearly** — filled background, bottom border, or bold label.
- **Don't use tabs for navigation that changes the URL** — tabs are within-page state changes. Use nav for page-level routing.
- **Overflow handling** — If tabs overflow their container on mobile, scroll horizontally. Never wrap tabs to a second line.
- **Tab content should be fast** — tab switching should feel instant. Don't put heavy data fetches behind tabs that only load on click.

---

## Breadcrumbs

Breadcrumbs show the hierarchical path to the current page.

### When to Use Breadcrumbs
- Any page **3 or more levels** deep in a hierarchy
- Products with complex nested navigation (CMS, file management, settings)
- When users may arrive directly at a deep page (from search, email link)

### When NOT to Use Breadcrumbs
- Flat sites with only 1–2 levels
- Single-page apps where URL doesn't reflect hierarchy
- Mobile (too small — use a back button instead)

### Breadcrumb Rules
- **Every crumb is a link** — except the current page (last item)
- **Current page is not a link** — it can be shown in muted color or without underline
- **Separator character** — use `/` or `›` — avoid `>` (looks like code) or `→` (implies direction)
- **Truncate long paths** — if the path is very deep, show first + last 2 levels: `Home / ... / Section / Current Page`
- **Match the page title** — the last breadcrumb should exactly match the `<h1>` of the current page

```html
<nav aria-label="Breadcrumb">
  <ol>
    <li><a href="/">Home</a></li>
    <li><a href="/projects">Projects</a></li>
    <li><a href="/projects/alpha">Project Alpha</a></li>
    <li aria-current="page">Settings</li>
  </ol>
</nav>
```

---

## Back Buttons

"Back" is a fundamental navigation primitive — and one of the most commonly broken patterns.

### Rules
- **Back goes to the previous screen, not the previous URL.** In a multi-step flow, pressing Back should go to the previous step, not the previous browser history entry.
- **Back in a modal closes the modal to the page behind it** — not to the previous page in history.
- **Back should not lose user data** — if the user has entered information, warn them before going back ("Go back? Your changes will be lost.") or auto-save.
- **Back button label should name the destination** — iOS convention: "< Projects" tells the user where they're going. Just "< Back" is acceptable but less helpful.
- **Always provide a way back** — any screen that can be reached should have an exit path. No dead ends.

### When to Show a Back Button
- Detail pages within a list (e.g. item detail → back to list)
- Steps in a flow (step 3 → back to step 2)
- Modals and drawers (close/back button in header)
- Any screen without primary navigation visible

---

## Mobile Navigation

### Bottom Navigation Bar
- **3–5 destinations** maximum. More than 5 = too crowded.
- **Always show labels** — icon-only bottom nav fails usability testing consistently.
- **Active state must be clear** — filled icon, label color change, or indicator dot.
- **Never use for secondary items** — keep primary destinations only.
- **Safe area** — respect iOS/Android safe area insets so content isn't hidden behind home indicator.

### Hamburger Menu
- Acceptable for **secondary or overflow navigation**.
- **Not acceptable** for primary navigation on mobile — it hides destinations, reducing discoverability by 50%+.
- If you have 3–5 primary destinations, use a bottom nav bar instead.

### Gestures
- **Swipe back** — respect native back gestures (iOS swipe from left edge, Android back button).
- Never intercept swipe gestures for something other than navigation without strong justification.

---

## Navigation Accessibility

- **`aria-current="page"`** — mark the active nav item with this attribute for screen readers
- **Skip navigation link** — provide a "Skip to main content" link as the first focusable element on each page. Essential for keyboard users who don't want to tab through the entire nav on every page.
- **Keyboard navigation** — nav items must be reachable and activatable by keyboard (Tab + Enter)
- **Focus management** — when a nav item opens a new section, move focus to the section heading or first interactive element

```html
<!-- Skip nav link (visually hidden until focused) -->
<a href="#main-content" class="skip-link">Skip to main content</a>

<!-- Active page indicator -->
<nav>
  <a href="/home">Home</a>
  <a href="/projects" aria-current="page">Projects</a>
  <a href="/settings">Settings</a>
</nav>
```

---

## Common Navigation Mistakes

| Mistake | Fix |
|---|---|
| Tabs used for top-level section navigation | Use nav bar or sidebar instead |
| No active state on current nav item | Add clear visual indicator (background, border, weight) |
| Breadcrumbs with non-clickable intermediate items | All crumbs except current page must be links |
| Back button goes to browser history, not app flow | Implement in-app back navigation in multi-step flows |
| Hamburger menu for primary nav on mobile | Use bottom nav bar for 3–5 primary destinations |
| Nav changes between sections (items appear/disappear) | Keep nav consistent on every page |
| No skip navigation link | Add `<a href="#main">Skip to main content</a>` as first element |
| Active nav item only differs by color | Add weight, background, or position indicator too |
