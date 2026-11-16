# Sonner API Reference

Exact props, types, and defaults. Options passed to `toast()` override the same options set via the Toaster's `toastOptions`.

## `<Toaster />`

| Prop | Type | Default | Description |
| --- | --- | --- | --- |
| `theme` | `string` | `'light'` | `'light'`, `'dark'`, or `'system'`. |
| `richColors` | `boolean` | `false` | Makes error and success states more colorful. |
| `expand` | `boolean` | `false` | Toasts expanded by default (otherwise they expand on hover). |
| `visibleToasts` | `number` | `3` | Amount of visible toasts. |
| `id` | `string` | – | Toaster id, targeted by `toast()`'s `toasterId` option. |
| `position` | `string` | `'bottom-right'` | `top-left`, `top-center`, `top-right`, `bottom-left`, `bottom-center`, `bottom-right`. |
| `closeButton` | `boolean` | `false` | Adds a close button to all toasts. |
| `offset` | `string \| number \| object` | `'32px'` | Offset from screen edges. Object form is per-side: `{ bottom: '24px', right: '16px' }`. |
| `mobileOffset` | `string \| number \| object` | `'16px'` | Offset when screen width < 600px. |
| `swipeDirections` | `array` | based on position | Allowed swipe-to-dismiss directions. |
| `dir` | `string` | `'ltr'` | Text directionality. |
| `hotkey` | `string` | `⌥/alt + T` | Keyboard shortcut that focuses the toaster area. |
| `invert` | `boolean` | `false` | Dark toasts in light mode and vice versa. |
| `toastOptions` | `object` | – | Default options applied to every toast (any `toast()` option below). |
| `gap` | `number` | `14` | Gap between toasts when expanded. |
| `icons` | `object` | – | Replace default icons: `{ success, info, warning, error, loading }`; `null` removes one. |

## `toast()` options

`toast(message, options)` — message is a string, JSX, or a function returning JSX. Returns the toast's id.

| Option | Type | Default | Description |
| --- | --- | --- | --- |
| `description` | `ReactNode` | – | Renders underneath the title; also accepts a function returning JSX. |
| `closeButton` | `boolean` | `false` | Adds a close button. |
| `invert` | `boolean` | `false` | Dark toast in light mode and vice versa. |
| `duration` | `number` | `4000` | Milliseconds before auto-close. `Infinity` persists the toast. |
| `position` | `string` | `'bottom-right'` | Position of this toast. |
| `dismissible` | `boolean` | `true` | If `false`, the user cannot dismiss the toast. |
| `icon` | `ReactNode` | – | Icon in front of the text; `null` removes the default. |
| `action` | `ReactNode \| { label, onClick }` | – | Primary button; clicking closes the toast unless `onClick` calls `event.preventDefault()`. |
| `cancel` | `ReactNode \| { label, onClick }` | – | Secondary button; clicking closes the toast. |
| `actionButtonStyle` | `object` | `{}` | Styles for the action button. |
| `cancelButtonStyle` | `object` | `{}` | Styles for the cancel button. |
| `id` | `string` | – | Custom id; calling `toast()` again with the same id updates the existing toast. |
| `testId` | `string` | – | Rendered as `data-testid` for e2e tests. |
| `toasterId` | `string` | – | Id of the toaster to render this toast in. |
| `style` | `object` | – | Inline styles for the toast. |
| `classNames` | `object` | – | Classes per part: `{ toast, title, description, actionButton, cancelButton, closeButton }`. Needs `!important` unless `unstyled`. |
| `unstyled` | `boolean` | `false` | Removes all default styles. |
| `onDismiss` | `(toast) => void` | – | Fires when the close button is clicked or the toast is swiped away. |
| `onAutoClose` | `(toast) => void` | – | Fires when the toast closes automatically after `duration`. |
| `containerAriaLabel` | `string` | `'Notifications'` | ARIA label for the toast container. |

## Functions

| Function | Purpose |
| --- | --- |
| `toast(message, opts?)` | Render a toast; returns its id. |
| `toast.success / .error / .info / .warning(message, opts?)` | Typed toast with matching icon. |
| `toast.loading(message, opts?)` | Toast with a spinner; update it by id. |
| `toast.promise(promise, { loading, success, error })` | Loading toast that resolves with the promise; `success`/`error` accept strings, JSX, functions of the result, or objects of toast options. |
| `toast.custom((t) => jsx, opts?)` | Headless toast — your JSX, Sonner's behavior. |
| `toast.dismiss(id?)` | Dismiss one toast, or all when called without an id. |
| `toast.getActiveToasts()` | All active toasts, usable outside React. |
| `useSonner()` | React hook returning `{ toasts }`. |
