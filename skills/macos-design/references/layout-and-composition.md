# Layout & Composition Reference

## Table of Contents
1. The Apple Layout Formula
2. Top Bar Design
3. Sidebar Navigation
4. Content Area
5. Empty States & Progressive Disclosure
6. Window Chrome & Traffic Lights
7. Multi-Window & System Integration

---

## 1. The Apple Layout Formula

Nearly every Apple utility app follows the same structural pattern:

```
┌─────────────────────────────────────────────────┐
│  Traffic Lights  │      Top Bar (Global Actions) │  ← ~50px, draggable
├──────────────────┼──────────────────────────────┤
│                  │                               │
│    Sidebar       │       Main Content            │
│   (Navigation)   │       (User's Data)           │
│                  │                               │
│                  │                               │
│                  │                               │
├──────────────────┴──────────────────────────────┤
│              Bottom Bar (optional)               │
└─────────────────────────────────────────────────┘
```

Apps that use this: Finder, Notes, Reminders, Calendar, Settings, Music, Shortcuts, Mail.

**Key insight**: Apps are containers for the user's information. Unlike landing pages (pre-generated content that doesn't change), apps hold data the user adds and manipulates. This is why the layout is user-focused with content at center stage.

### When to Skip the Sidebar

If navigation is minimal (just browsing + searching), drop the sidebar entirely. This gives extra room for content. The app becomes essentially a single-screen utility — which is how most of Apple's best tools work. They do one thing and do it well, so the UI stays hyperfocused.

---

## 2. Top Bar Design

The top bar serves global-level actions: search, view toggles, sort, new item.

**Rules:**
- Height: ~50px (this zone doubles as the window drag area)
- Keep it sparse — do NOT clutter with actions. Let it breathe
- Traffic lights can live here, flush left, treated as just another element
- Search is almost always present and prominent
- Use segmented controls for view switching (grid/list/etc.)

**Example top bar structure:**
```
[● ● ●]  [< Back]  Browse        [Search.............]  [+ New]  [⚙]
```

**Common mistakes:**
- Too many buttons crowding the drag zone
- Making the top bar feel like a toolbar instead of a title bar
- Forgetting that users need to grab this area to move the window

---

## 3. Sidebar Navigation

When your app needs a sidebar:

- Width: 200-260px, optionally resizable
- Background: slightly different shade than content (use vibrancy/blur in native apps)
- Sections grouped with small caps headers
- Active item: subtle highlight, not a loud color block
- Icons: SF Symbols style — thin, monoline, 16-20px
- Collapsible on smaller windows

**When NOT to use a sidebar:**
- App has fewer than 3 navigation destinations
- App is a single-purpose utility
- Content benefits more from full width

---

## 4. Content Area

The content area is the star. Everything else exists to support it.

**Principles:**
- Minimize UI chrome around content — the app is a container, not a frame
- Images and media should be large and breathable
- Grid layouts: consistent gaps (12-16px), responsive columns
- List layouts: generous row height, hover states, clear hierarchy
- Detail views: slide-out panels preferred over full page navigation (keeps context)

**Grid layout guidelines:**
```
Small window:   2 columns
Medium window:  3 columns  
Large window:   4-5 columns
Gap:            12-16px
Padding:        16-24px from edges
Corner radius:  8px on cards
```

**Detail / Preview pattern:**
Instead of navigating to a new page, slide out a panel from the right. This maintains context — the user can still see the grid behind the preview. Include a floating action bar in the preview for common actions (copy, delete, share, etc.).

---

## 5. Empty States & Progressive Disclosure

**Empty state**: When there's no content, show a clean, inviting placeholder.
- Centered in the content area
- Simple icon or illustration (not busy)
- One line of text explaining what goes here
- A clear CTA to get started
- All filters, toolbars, and secondary UI should be HIDDEN — they're useless without content

**Progressive disclosure**: Only show UI when the user needs it.
- Filters appear after content exists
- Metadata appears on hover or click, not by default
- Advanced options tucked behind a "..." menu or settings
- Search expands from a collapsed state when triggered

**Ask yourself**: What is the minimum UI needed to let the content shine?

---

## 6. Window Chrome & Traffic Lights

**Traffic light buttons** (close, minimize, maximize):
- Always positioned top-left
- Integrate them INTO the UI — they should feel like part of the sidebar or top bar, not a separate system element
- Standard spacing: 8px from top-left corner, 8px between dots
- Size: 12px diameter circles
- Colors: red (#FF5F57), yellow (#FEBC2E), green (#28C840)
- On hover: show ×, −, + icons inside
- When window is inactive: all three become gray (#CDCDCD)

**Window properties:**
- Corner radius: 10px (macOS standard)
- Shadow: layered — inner subtle shadow + outer soft spread
- Border: 0.5px solid with low opacity for definition
- Background: respect vibrancy when possible (slight transparency + blur)

**Simulating in web/React:**
```css
.macos-window {
  border-radius: 10px;
  box-shadow:
    0 0 0 0.5px rgba(0,0,0,0.1),
    0 2px 8px rgba(0,0,0,0.08),
    0 8px 30px rgba(0,0,0,0.12);
  overflow: hidden;
}
```

---

## 7. Multi-Window & System Integration

Native macOS apps don't live only in their main window. Consider:

**Popovers**: Small floating panels for settings, quick actions, or confirmations. Appear near the triggering element with an arrow pointing to it.

**Panels / Sheets**: Slide down from the top of the window for modal-ish interactions that don't take over the whole screen.

**Quick-access windows**: Triggered by global keyboard shortcuts (like Spotlight via Cmd+Space). These float above everything, have no traffic lights, and are minimal — just the essential input + action. They should:
- Slide in quietly from the side or fade in from center
- Have backdrop blur (native vibrancy feel)
- Disappear on Escape or after completing the action
- Collapse into a toast notification on success

**Toast notifications**: After an action completes, show a small confirmation that slides away automatically. This is optimistic UI — assume success, process in background.

**System tray / Menu bar**: Some apps live primarily in the menu bar (like Paste, Bartender). Consider if your app benefits from always-available access without being a full window.

**Share sheet**: Apple's universal share button (square with up-arrow). Include it for any content that might leave your app.
