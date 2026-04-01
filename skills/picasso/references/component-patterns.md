# Component Patterns Reference

Standard component taxonomy, naming conventions, and state patterns drawn from 90+ real-world design systems and 2,500+ implementations (sourced from component.gallery).

## Standard Component Names

Use these names consistently. When building a component, check this list first. Do not invent new names for solved patterns.

### Navigation
- **Navbar / Navigation Bar**: Top-level site navigation. Contains logo, links, actions.
- **Sidebar / Side Navigation**: Vertical navigation panel, typically on the left.
- **Breadcrumb**: Shows the user's location in a hierarchy. e.g., Home > Products > Shoes.
- **Tabs**: Horizontal set of toggles for switching between views within a section.
- **Pagination**: Controls for navigating between pages of content.
- **Bottom Navigation / Tab Bar**: Mobile-only bottom navigation with 3-5 icon+label items.
- **Menu / Dropdown Menu**: A list of options revealed on click, typically from a button.
- **Command Palette / Command Menu**: Keyboard-driven search-and-action overlay (Cmd+K pattern).

### Content
- **Card**: A bounded container for a unit of content (image, title, description, action).
- **Accordion / Disclosure**: Expandable/collapsible sections in a vertical stack.
- **Carousel / Slider**: Multiple slides navigated via swipe, scroll, or buttons.
- **Table / Data Table**: Structured rows and columns for tabular data.
- **List / List Item**: Ordered or unordered vertical sequence of items.
- **Tree View**: Nested hierarchical content (file explorer, category browser).
- **Timeline**: Chronological sequence of events.
- **Empty State**: Placeholder shown when a section has no content yet.

### Input
- **Text Input / Text Field**: Single-line text entry.
- **Textarea**: Multi-line text entry.
- **Select / Dropdown**: Choose one option from a list.
- **Combobox / Autocomplete**: Text input with filtered dropdown suggestions.
- **Checkbox**: Binary on/off selection (multiple selections allowed).
- **Radio / Radio Group**: Select exactly one option from a set.
- **Toggle / Switch**: Binary on/off with immediate effect (no form submission needed).
- **Slider / Range**: Select a value within a numeric range by dragging.
- **Date Picker**: Calendar-based date selection.
- **File Upload**: Interface for selecting and uploading files.
- **Search Input**: Text input with search semantics (clear button, submit on enter).

### Feedback
- **Alert / Banner**: Non-interactive message at the top of a page or section.
- **Toast / Snackbar**: Temporary notification that auto-dismisses. Bottom of screen.
- **Modal / Dialog**: Overlay requiring user attention before returning to the page.
- **Popover**: Small overlay anchored to a trigger element, often for contextual info.
- **Tooltip**: Brief label shown on hover/focus, never interactive.
- **Progress Bar**: Linear indicator of completion (determinate or indeterminate).
- **Spinner / Loading Indicator**: Circular animation indicating a pending operation.
- **Skeleton / Placeholder**: Gray shapes matching expected content layout during load.
- **Badge / Tag / Chip**: Small label for status, category, or count.

### Actions
- **Button**: Primary interactive element for triggering actions.
- **Icon Button**: Button with only an icon (must have aria-label).
- **Button Group**: Set of related buttons displayed together.
- **Floating Action Button (FAB)**: Prominent circular button for the primary action (mobile).
- **Link / Anchor**: Navigation to another page or resource.

### Layout
- **Container**: Max-width wrapper centering content on the page.
- **Divider / Separator**: Visual line separating content sections.
- **Grid**: Multi-column layout system.
- **Stack**: Vertical or horizontal arrangement with consistent spacing.
- **Aspect Ratio**: Container maintaining a fixed width:height ratio.

## Component State Matrix

Every interactive component needs these states defined:

| State | Visual Treatment |
|---|---|
| Default | Base appearance |
| Hover | Subtle change: background lightens/darkens, cursor changes |
| Focus | High-contrast outline (2px accent, 2px offset) |
| Active / Pressed | Slight scale-down (0.97-0.98), darkened background |
| Disabled | 50% opacity, cursor: not-allowed, no hover/focus effects |
| Loading | Spinner or skeleton replacing content, pointer-events: none |
| Error | Error-colored border, inline error message |
| Selected / Active | Accent background or border, checkmark indicator |
| Dragging | Elevated shadow, slight rotation, reduced opacity on source |

## Compound Component Pattern

For components with multiple sub-parts, use the dot notation compound pattern:

```tsx
<Dialog>
  <Dialog.Trigger>Open</Dialog.Trigger>
  <Dialog.Content>
    <Dialog.Title>Confirm</Dialog.Title>
    <Dialog.Description>Are you sure?</Dialog.Description>
    <Dialog.Footer>
      <Dialog.Close>Cancel</Dialog.Close>
      <Button>Confirm</Button>
    </Dialog.Footer>
  </Dialog.Content>
</Dialog>
```

This pattern appears in: Radix UI, shadcn/ui, Headless UI, Reach UI, Ark UI.

## Component Sizing Convention

Use a consistent sizing scale across all components:

| Size | Height | Font Size | Padding | Use Case |
|---|---|---|---|---|
| xs | 28px | 12px | 4px 8px | Dense UIs, inline tags |
| sm | 32px | 13px | 6px 12px | Secondary actions, compact forms |
| md | 40px | 14px | 8px 16px | Default for most components |
| lg | 48px | 16px | 12px 24px | Primary actions, hero sections |
| xl | 56px | 18px | 16px 32px | Landing page CTAs |
