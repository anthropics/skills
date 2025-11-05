# USS Reference

Complete reference for Unity Style Sheets (USS) - Unity's CSS-inspired styling system.

## File Structure

USS files use `.uss` extension and follow CSS syntax with Unity-specific extensions.

```css
/* Basic structure */
SelectorType {
    property-name: value;
    another-property: value;
}
```

## Selectors

### Type Selector

Matches elements by type name:

```css
Button {
    background-color: blue;
}

Label {
    color: white;
}
```

### Class Selector

Matches elements with specific class (use `.` prefix):

```css
.primary-button {
    background-color: rgb(0, 120, 215);
    color: white;
}

.error-text {
    color: red;
}
```

Apply multiple classes in C# or UXML:
```csharp
element.AddToClassList("primary-button");
element.AddToClassList("large");
```

```xml
<ui:Button class="primary-button large" />
```

### Name Selector (ID)

Matches element by name attribute (use `#` prefix):

```css
#submit-button {
    width: 200px;
    height: 50px;
}

#title-label {
    font-size: 24px;
    -unity-font-style: bold;
}
```

### Universal Selector

Matches all elements:

```css
* {
    margin: 0;
    padding: 0;
}
```

### Descendant Selector

Matches nested elements:

```css
/* Label inside container */
.container Label {
    color: gray;
}

/* Button inside form inside panel */
.panel .form Button {
    margin: 5px;
}
```

### Child Selector

Matches direct children only (use `>`):

```css
.toolbar > Button {
    margin-right: 10px;
}
```

### Multiple Selectors

Comma-separated list:

```css
Button, Toggle, TextField {
    border-width: 1px;
    border-color: gray;
}
```

### Combining Selectors

```css
/* Button with primary-button class */
Button.primary-button {
    background-color: blue;
}

/* Element with name="header" and class="large" */
#header.large {
    height: 100px;
}
```

## Pseudo-Classes

State-based selectors:

```css
/* Hover state */
Button:hover {
    background-color: rgb(70, 170, 220);
}

/* Active/pressed state */
Button:active {
    background-color: rgb(30, 100, 180);
}

/* Focus state */
TextField:focus {
    border-color: rgb(0, 120, 215);
    border-width: 2px;
}

/* Disabled state */
Button:disabled {
    opacity: 0.5;
}

/* Checked state (Toggle) */
Toggle:checked {
    background-color: green;
}

/* Root element */
:root {
    --primary-color: rgb(0, 120, 215);
}
```

## Layout Properties

### Size

```css
.element {
    /* Fixed size */
    width: 200px;
    height: 100px;

    /* Percentage of parent */
    width: 50%;
    height: 100%;

    /* Auto (fit content) */
    width: auto;
    height: auto;

    /* Min/Max constraints */
    min-width: 100px;
    max-width: 500px;
    min-height: 50px;
    max-height: 300px;
}
```

### Margin and Padding

```css
.element {
    /* All sides */
    margin: 10px;
    padding: 15px;

    /* Individual sides */
    margin-top: 5px;
    margin-right: 10px;
    margin-bottom: 5px;
    margin-left: 10px;

    /* Shorthand (top, right, bottom, left) */
    margin: 5px 10px 5px 10px;

    /* Shorthand (vertical, horizontal) */
    padding: 10px 20px;
}
```

### Flexbox Layout

UI Toolkit uses Flexbox for layout:

```css
.container {
    /* Flex direction */
    flex-direction: row;          /* horizontal (default) */
    flex-direction: column;       /* vertical */
    flex-direction: row-reverse;  /* reverse horizontal */
    flex-direction: column-reverse; /* reverse vertical */

    /* Main axis alignment (justify-content) */
    justify-content: flex-start;  /* start (default) */
    justify-content: center;      /* center */
    justify-content: flex-end;    /* end */
    justify-content: space-between; /* space between items */
    justify-content: space-around;  /* space around items */

    /* Cross axis alignment (align-items) */
    align-items: flex-start;    /* start */
    align-items: center;        /* center */
    align-items: flex-end;      /* end */
    align-items: stretch;       /* stretch to fill (default) */

    /* Wrap behavior */
    flex-wrap: nowrap;  /* single line (default) */
    flex-wrap: wrap;    /* multi-line */
    flex-wrap: wrap-reverse; /* multi-line reversed */

    /* Content alignment (multi-line) */
    align-content: flex-start;
    align-content: center;
    align-content: flex-end;
    align-content: space-between;
    align-content: space-around;
    align-content: stretch;
}

.flex-item {
    /* Flex grow factor */
    flex-grow: 0; /* don't grow (default) */
    flex-grow: 1; /* grow to fill available space */

    /* Flex shrink factor */
    flex-shrink: 1; /* can shrink (default) */
    flex-shrink: 0; /* don't shrink */

    /* Flex basis (initial size) */
    flex-basis: auto;   /* use width/height */
    flex-basis: 200px;  /* fixed size */
    flex-basis: 50%;    /* percentage */

    /* Individual alignment */
    align-self: auto;       /* use parent's align-items */
    align-self: flex-start;
    align-self: center;
    align-self: flex-end;
    align-self: stretch;
}
```

Common flex patterns:

```css
/* Horizontal center */
.h-center {
    flex-direction: row;
    justify-content: center;
}

/* Vertical center */
.v-center {
    flex-direction: column;
    justify-content: center;
}

/* Center both axes */
.center {
    justify-content: center;
    align-items: center;
}

/* Evenly spaced row */
.row-spaced {
    flex-direction: row;
    justify-content: space-between;
}

/* Fill available space */
.fill {
    flex-grow: 1;
}
```

### Position

```css
.element {
    /* Relative (default, follows flow) */
    position: relative;

    /* Absolute (removed from flow) */
    position: absolute;
    top: 10px;
    left: 20px;
    right: 30px;
    bottom: 40px;
}
```

## Visual Properties

### Colors

```css
.element {
    /* RGB */
    color: rgb(255, 0, 0);
    background-color: rgb(50, 100, 150);

    /* RGBA */
    color: rgba(255, 0, 0, 0.5);

    /* Hex (Unity 2021.2+) */
    color: #FF0000;
    background-color: #32649680; /* with alpha */

    /* Named colors */
    color: red;
    background-color: transparent;
}
```

### Background

```css
.element {
    background-color: white;

    /* Background image */
    background-image: url('Assets/Textures/bg.png');
    background-image: resource('Textures/bg'); /* from Resources */

    /* Background image properties */
    -unity-background-scale-mode: stretch-to-fill; /* default */
    -unity-background-scale-mode: scale-and-crop;
    -unity-background-scale-mode: scale-to-fit;

    -unity-background-image-tint-color: rgba(255, 255, 255, 1);
}
```

### Borders

```css
.element {
    /* Border width (all sides) */
    border-width: 2px;

    /* Individual sides */
    border-top-width: 1px;
    border-right-width: 2px;
    border-bottom-width: 1px;
    border-left-width: 2px;

    /* Border color */
    border-color: black;
    border-top-color: red;
    border-right-color: blue;

    /* Border radius */
    border-radius: 5px;
    border-top-left-radius: 10px;
    border-top-right-radius: 10px;
    border-bottom-left-radius: 10px;
    border-bottom-right-radius: 10px;
}
```

### Opacity and Visibility

```css
.element {
    /* Opacity (0 = transparent, 1 = opaque) */
    opacity: 0.5;

    /* Visibility */
    visibility: visible;
    visibility: hidden; /* invisible but takes space */

    /* Display */
    display: flex;    /* visible and in layout */
    display: none;    /* invisible and removed from layout */
}
```

### Overflow

```css
.container {
    overflow: visible; /* content can overflow (default) */
    overflow: hidden;  /* clip overflowing content */
    overflow: scroll;  /* always show scrollbars */
}
```

## Text Properties

### Font

```css
.text {
    /* Font size */
    font-size: 16px;
    font-size: 12pt; /* Unity 2022+, 1pt = 1.33px */

    /* Unity font asset */
    -unity-font: url('Assets/Fonts/MyFont.ttf');
    -unity-font: resource('Fonts/MyFont');

    /* Font style */
    -unity-font-style: normal;
    -unity-font-style: bold;
    -unity-font-style: italic;
    -unity-font-style: bold-and-italic;

    /* Font definition (TextCore) */
    -unity-font-definition: url('Assets/Fonts/MyFont SDF.asset');
}
```

### Text Alignment

```css
.text {
    /* Horizontal alignment */
    -unity-text-align: upper-left;
    -unity-text-align: upper-center;
    -unity-text-align: upper-right;
    -unity-text-align: middle-left;
    -unity-text-align: middle-center;
    -unity-text-align: middle-right;
    -unity-text-align: lower-left;
    -unity-text-align: lower-center;
    -unity-text-align: lower-right;

    /* Text wrapping */
    white-space: normal;    /* wrap text */
    white-space: nowrap;    /* don't wrap */

    /* Text overflow */
    text-overflow: clip;    /* cut off */
    text-overflow: ellipsis; /* show ... */
}
```

### Text Color and Shadow

```css
.text {
    color: white;

    /* Text shadow (Unity 2021.2+) */
    text-shadow: 2px 2px 4px rgba(0, 0, 0, 0.5);
    /* offset-x offset-y blur-radius color */
}
```

## Unity-Specific Properties

### Slice (9-Slice Scaling)

```css
.element {
    -unity-slice-left: 10;
    -unity-slice-top: 10;
    -unity-slice-right: 10;
    -unity-slice-bottom: 10;

    /* Or use scale instead of slice for sprite borders */
    -unity-background-scale-mode: scale-and-crop;
}
```

### Overflow Clip Box

```css
.element {
    -unity-overflow-clip-box: padding-box; /* default */
    -unity-overflow-clip-box: content-box;
}
```

### Paragraph Spacing

```css
.text {
    -unity-paragraph-spacing: 10px;
}
```

## Transitions and Animations

### Transitions

Smooth property changes:

```css
.button {
    background-color: blue;
    transition-property: background-color;
    transition-duration: 0.3s;
    transition-timing-function: ease-in-out;
    transition-delay: 0s;
}

.button:hover {
    background-color: lightblue;
}

/* Shorthand */
.button {
    transition: background-color 0.3s ease-in-out;
}

/* Multiple properties */
.button {
    transition: background-color 0.3s, border-color 0.2s;
}

/* All properties */
.button {
    transition-property: all;
    transition-duration: 0.3s;
}
```

**Timing functions:**
- `ease` - slow start, fast middle, slow end
- `ease-in` - slow start
- `ease-out` - slow end
- `ease-in-out` - slow start and end
- `linear` - constant speed
- `ease-in-sine`, `ease-out-sine`, `ease-in-out-sine`
- `ease-in-cubic`, `ease-out-cubic`, `ease-in-out-cubic`
- `ease-in-circ`, `ease-out-circ`, `ease-in-out-circ`
- `ease-in-elastic`, `ease-out-elastic`, `ease-in-out-elastic`
- `ease-in-back`, `ease-out-back`, `ease-in-out-back`
- `ease-in-bounce`, `ease-out-bounce`, `ease-in-out-bounce`

### Rotate, Scale, Translate (Unity 2021.2+)

```css
.element {
    /* Rotate */
    rotate: 45deg;
    rotate: 0.785rad; /* radians */

    /* Scale */
    scale: 1.5;              /* uniform */
    scale: 1.5 2;            /* x y */

    /* Translate */
    translate: 10px 20px;    /* x y */

    /* Transform origin */
    transform-origin: center; /* default */
    transform-origin: top-left;
    transform-origin: 50% 50%; /* x% y% */
    transform-origin: 10px 20px; /* x y */
}
```

## Cursor

```css
.element {
    cursor: url('Assets/Cursors/pointer.png');
    cursor: resource('Cursors/pointer');

    /* Or default cursors */
    cursor: default;
    cursor: arrow;
    cursor: text;
    cursor: resize-vertical;
    cursor: resize-horizontal;
    cursor: link;
    cursor: slide-arrow;
    cursor: resize-up-right;
    cursor: resize-up-left;
    cursor: move-arrow;
    cursor: rotate-arrow;
    cursor: scale-arrow;
    cursor: arrow-plus;
    cursor: arrow-minus;
    cursor: pan;
    cursor: orbit;
    cursor: zoom;
    cursor: fps;
    cursor: split-resize-up-down;
    cursor: split-resize-left-right;
}
```

## CSS Variables (Custom Properties)

Define and reuse values:

```css
:root {
    --primary-color: rgb(0, 120, 215);
    --secondary-color: rgb(100, 100, 100);
    --border-radius: 5px;
    --spacing: 10px;
}

.button {
    background-color: var(--primary-color);
    border-radius: var(--border-radius);
    margin: var(--spacing);
}

.button:hover {
    background-color: var(--secondary-color);
}

/* With fallback */
.element {
    color: var(--text-color, black);
}
```

## Specificity and Cascading

Specificity order (highest to lowest):

1. Inline styles (highest)
2. ID selectors (#name)
3. Class selectors (.class), pseudo-classes (:hover)
4. Type selectors (Button)
5. Universal selector (*)

**Example:**
```css
/* Specificity: 1 */
Button {
    color: blue;
}

/* Specificity: 10 */
.primary {
    color: green;
}

/* Specificity: 100 */
#submit {
    color: red;
}

/* Specificity: 111 */
#submit.primary Button {
    color: purple;
}
```

## Media Queries (Not Supported)

Unity UI Toolkit does not support CSS media queries. Use C# to handle responsive layouts.

## Comments

```css
/* Single line comment */

/*
 * Multi-line
 * comment
 */
```

## Best Practices

### 1. Use BEM Naming Convention

```css
/* Block */
.card { }

/* Element */
.card__title { }
.card__content { }
.card__button { }

/* Modifier */
.card--highlighted { }
.card__button--primary { }
```

### 2. Organize Styles Hierarchically

```css
/* Base styles */
* {
    margin: 0;
    padding: 0;
}

/* Layout containers */
.container { }
.row { }
.column { }

/* Components */
.button { }
.card { }
.modal { }

/* Utilities */
.text-center { }
.hide { }
.show { }
```

### 3. Use Variables for Consistency

```css
:root {
    --color-primary: rgb(0, 120, 215);
    --color-secondary: rgb(100, 100, 100);
    --color-success: rgb(0, 200, 0);
    --color-error: rgb(200, 0, 0);

    --spacing-xs: 4px;
    --spacing-sm: 8px;
    --spacing-md: 16px;
    --spacing-lg: 24px;

    --border-radius: 4px;
    --transition-speed: 0.3s;
}
```

### 4. Avoid Over-Nesting

```css
/* Bad - too specific */
.container .header .nav .item .link {
    color: blue;
}

/* Good - flatter hierarchy */
.nav-link {
    color: blue;
}
```

### 5. Prefer USS Files Over Inline Styles

Inline styles create higher memory overhead and are harder to maintain.

### 6. Group Related Properties

```css
.element {
    /* Layout */
    width: 200px;
    height: 100px;
    margin: 10px;
    padding: 5px;

    /* Visual */
    background-color: white;
    border-width: 1px;
    border-color: gray;
    border-radius: 5px;

    /* Text */
    color: black;
    font-size: 14px;
    -unity-text-align: middle-center;

    /* Other */
    opacity: 1;
    transition: all 0.3s;
}
```

## Common Patterns

### Button Styles

```css
.button {
    background-color: rgb(0, 120, 215);
    color: white;
    border-radius: 4px;
    padding: 8px 16px;
    border-width: 0;
    transition: background-color 0.2s;
}

.button:hover {
    background-color: rgb(0, 140, 235);
}

.button:active {
    background-color: rgb(0, 100, 195);
}

.button:disabled {
    background-color: rgb(150, 150, 150);
    opacity: 0.6;
}
```

### Card Component

```css
.card {
    background-color: white;
    border-radius: 8px;
    border-width: 1px;
    border-color: rgb(220, 220, 220);
    padding: 16px;
    margin: 8px;
}

.card__title {
    font-size: 18px;
    -unity-font-style: bold;
    margin-bottom: 8px;
}

.card__content {
    font-size: 14px;
    color: rgb(100, 100, 100);
}
```

### Flexbox Layouts

```css
.flex-row {
    flex-direction: row;
    align-items: center;
}

.flex-column {
    flex-direction: column;
}

.flex-center {
    justify-content: center;
    align-items: center;
}

.flex-between {
    justify-content: space-between;
}

.flex-1 {
    flex-grow: 1;
}
```

## Troubleshooting

**Styles not applying:**
- Check USS file is loaded via UIDocument or styleSheets.Add()
- Verify selector specificity
- Check for typos in property names
- Ensure element has proper class/name

**Layout not working as expected:**
- Check parent flex-direction
- Verify flex-grow, flex-shrink values
- Check min/max width/height constraints
- Use UI Toolkit Debugger to inspect computed styles

**Performance issues:**
- Minimize use of inline styles
- Reduce deep selector nesting
- Avoid unnecessary transitions on many elements
- Use classes instead of complex selectors
