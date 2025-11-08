# React Spectrum Theming and Customization Guide

Complete guide to customizing React Spectrum themes, including dark mode and custom color systems.

## Theme System Overview

React Spectrum theming is built on CSS custom properties (variables) that define:
- Color scales (12-step perceptual matching)
- Typography scales
- Spacing units
- Border radius
- Shadows
- Opacity values
- Animation timing

This allows complete theme customization while maintaining design consistency and accessibility.

## Built-in Themes

### Light Theme
Standard light theme with dark text on light backgrounds.

```jsx
import { lightTheme } from '@adobe/react-spectrum';

<Provider theme={lightTheme}>
  <App />
</Provider>
```

### Dark Theme
Perceptually matched dark theme optimized for reduced eye strain.

```jsx
import { darkTheme } from '@adobe/react-spectrum';

<Provider theme={darkTheme}>
  <App />
</Provider>
```

### Automatic Theme Selection
Use system preference to select theme.

```jsx
import { Provider, lightTheme, darkTheme } from '@adobe/react-spectrum';

function App() {
  const prefersDark = window.matchMedia(
    '(prefers-color-scheme: dark)'
  ).matches;

  return (
    <Provider theme={prefersDark ? darkTheme : lightTheme}>
      <YourApp />
    </Provider>
  );
}
```

## Color System

### Semantic Color Tokens
Spectrum uses semantic color tokens instead of literal color names.

**Semantic colors:**
- `primary`: Main brand color
- `secondary`: Supporting brand color
- `positive`: Success/confirmation color
- `notice`: Warning/caution color
- `negative`: Error/destructive color
- `info`: Information color
- `neutral`: Neutral color

**Color scales:**
Each color has a 12-step scale:
- `gray-50` through `gray-900` (lightest to darkest)
- `blue-50` through `blue-900`
- etc. for each color family

### Using Color Tokens in CSS

```css
/* Theme variables in CSS */
.my-component {
  color: var(--spectrum-global-color-gray-800);
  background-color: var(--spectrum-global-color-blue-50);
  border-color: var(--spectrum-global-color-blue-200);
}
```

### Using Color Tokens in React

```jsx
import { View, Text } from '@adobe/react-spectrum';

<View backgroundColor="blue-50" padding="size-200">
  <Text color="gray-900">Styled text</Text>
</View>
```

## Creating Custom Themes

### Theme Object Structure

```typescript
interface Theme {
  name: string;
  colors: {
    [colorFamily: string]: {
      [step: string]: string; // 50, 100, 200, ... 900
    };
  };
  typography?: {
    [size: string]: {
      fontSize: string;
      lineHeight: string;
      fontWeight: number;
    };
  };
  dimension?: {
    size: {
      [step: string]: string;
    };
    borderRadius?: {
      [name: string]: string;
    };
    shadow?: {
      [level: string]: string;
    };
  };
}
```

### Basic Custom Theme

```jsx
const customTheme = {
  name: 'custom',
  colors: {
    blue: {
      50: '#f0f4ff',
      100: '#e1e8ff',
      200: '#c2d0ff',
      300: '#a3b8ff',
      400: '#84a0ff',
      500: '#6b8cff', // primary
      600: '#5272e8',
      700: '#3958d1',
      800: '#203ebc',
      900: '#0824a5',
    },
    gray: {
      50: '#fafbfc',
      100: '#f5f6f8',
      200: '#ebeef3',
      300: '#d5dae5',
      400: '#b0b8ca',
      500: '#8b93a8',
      600: '#737f8f',
      700: '#4f5861',
      800: '#2f3439',
      900: '#121518',
    },
    // ... other color families
  },
};

<Provider theme={customTheme}>
  <App />
</Provider>
```

### Using Spectrum's Color Utility

Spectrum provides color scaling utilities for generating color scales:

```jsx
import { createTheme } from '@adobe/react-spectrum';

const customTheme = createTheme({
  colorScheme: 'light',
  colors: {
    primary: '#0078d4',  // Brand color
    secondary: '#6b8cff',
    positive: '#11a538',
    notice: '#f8860b',
    negative: '#e63946',
  },
});

<Provider theme={customTheme}>
  <App />
</Provider>
```

## Dark Mode Best Practices

### 1. Use Perceptual Color Matching
Dark theme should maintain visual hierarchy and contrast.

```jsx
// Good: Spectrum's dark theme maintains hierarchy
<Provider theme={darkTheme}>
  <App />
</Provider>

// Avoid: Simply inverting colors
const inverseTheme = {
  // ...colors just inverted from light theme
};
```

### 2. Test Contrast Ratios
Ensure text meets WCAG AAA standards (7:1 minimum).

```jsx
// Test with accessibility tools
// Light text on dark background
// Color: #ffffff (white)
// Background: #121518 (dark gray)
// Contrast ratio: 15.3:1 (AAA compliant)
```

### 3. Avoid Pure White/Black
Use slightly tinted backgrounds for reduced eye strain.

```css
/* Better for dark mode */
--spectrum-global-color-gray-50: #fafbfc;   /* Not pure white */
--spectrum-global-color-gray-900: #121518;  /* Not pure black */
```

### 4. High Contrast Indicators
Ensure interactive elements remain visible.

```jsx
// Use focus rings
<Button autoFocus>
  Click me
</Button>

// Sufficient color contrast for disabled state
<Button isDisabled>Disabled</Button>
```

## Typography Customization

### Font Size Scale
Spectrum uses a modular font scale.

**Standard sizes:**
- `size-75`: 12px (caption, small labels)
- `size-85`: 14px (small text)
- `size-100`: 16px (body text, default)
- `size-200`: 18px (larger body)
- `size-300`: 20px (heading 6)
- `size-400`: 24px (heading 5)
- `size-500`: 28px (heading 4)
- `size-600`: 32px (heading 3)
- `size-700`: 36px (heading 2)
- `size-800`: 40px (heading 1)

### Font Weight Tokens
- `100`: Thin
- `200`: Extra light
- `300`: Light
- `400`: Regular (normal)
- `500`: Medium
- `600`: Semibold
- `700`: Bold
- `800`: Extra bold
- `900`: Black

### Custom Typography

```jsx
<Text size="size-300" weight="bold" color="gray-900">
  Custom heading style
</Text>

// Or using CSS variables
const text = {
  fontSize: 'var(--spectrum-global-dimension-size-300)',
  fontWeight: 700,
  color: 'var(--spectrum-global-color-gray-900)',
};
```

## Spacing System

### Spacing Scale
Base unit: 8px

**Scale steps:**
- `size-50`: 4px
- `size-75`: 6px
- `size-100`: 8px
- `size-200`: 16px
- `size-300`: 24px
- `size-400`: 32px
- `size-500`: 40px
- `size-600`: 48px
- `size-800`: 64px
- `size-1000`: 80px
- `size-1200`: 96px
- `size-1600`: 128px
- `size-2000`: 160px
- `size-3200`: 256px

### Using Spacing

```jsx
import { Flex, View } from '@adobe/react-spectrum';

// Using gap
<Flex gap="size-200" direction="row">
  <Item />
  <Item />
</Flex>

// Using padding
<View padding="size-300">
  Content
</View>

// Using margin (via CSS)
const style = {
  marginTop: 'var(--spectrum-global-dimension-size-200)',
};
```

## Border Radius Customization

### Predefined Radii
- `xsmall`: 4px (small components)
- `small`: 6px (buttons, inputs)
- `medium`: 8px (dialogs, cards)
- `large`: 12px (large components)
- `xlarge`: 16px (large modals)
- `full`: 50% (circles, pills)

### Usage

```jsx
<View borderRadius="medium" backgroundColor="gray-50">
  Rounded corner container
</View>
```

## Shadow System

### Elevation Shadows
Spectrum uses elevation shadows for depth.

**Levels:**
- `elevation-1`: Small shadow (tooltips, popovers)
- `elevation-2`: Medium shadow (cards, dropdowns)
- `elevation-3`: Large shadow (modals, dialogs)
- `elevation-4`: Extra large shadow (floating panels)

### CSS Usage

```css
.my-card {
  box-shadow: var(--spectrum-global-shadow-size-100);
}

.my-modal {
  box-shadow: var(--spectrum-global-shadow-size-400);
}
```

## Responsive Design Tokens

### Breakpoints
Spectrum provides responsive sizing tokens.

**Available breakpoints:**
- `base`: 0px (mobile first)
- `S`: 640px (tablet)
- `M`: 768px (small desktop)
- `L`: 1024px (desktop)
- `XL`: 1280px (large desktop)

### Responsive Sizing

```jsx
<View
  width={{
    base: '100%',    // Mobile: full width
    S: '90%',        // Tablet: 90%
    M: '80%',        // Small desktop: 80%
    L: '70%',        // Desktop: 70%
    XL: '60%',       // Large desktop: 60%
  }}
/>

<Flex
  gap={{
    base: 'size-100',  // Mobile: 8px
    M: 'size-200',     // Tablet+: 16px
  }}
>
  Items
</Flex>
```

## Animation Timing

### Duration Tokens
- `duration-100`: 100ms
- `duration-200`: 200ms
- `duration-300`: 300ms
- `duration-400`: 400ms
- `duration-500`: 500ms

### Easing Functions
- `easing-linear`: Linear
- `easing-ease-in`: Ease in
- `easing-ease-out`: Ease out
- `easing-ease-in-out`: Ease in-out

### CSS Usage

```css
.my-element {
  transition: opacity var(--spectrum-global-animation-duration-200)
              var(--spectrum-global-animation-ease-in-out);
}
```

## RTL Support

Spectrum automatically handles right-to-left languages.

### Logical Properties
Use logical properties instead of directional:

```jsx
// Good: Works in both LTR and RTL
<View paddingInline="size-200">  // Horizontal padding
  Content
</View>

// Avoid: Directional properties
<View paddingLeft="size-200">  // Only works LTR
  Content
</View>
```

### Text Direction

```jsx
<Provider theme={lightTheme} locale="ar-SA">
  <App />
</Provider>
```

## Performance Optimization

### CSS Variable Overhead
While CSS variables are powerful, consider performance:

1. **Minimal variable usage** for frequently rendered components
2. **Cache computed values** in JavaScript
3. **Use static classes** for frequently used patterns

### Theming Wrapper Component

```jsx
import { useMemo } from 'react';
import { Provider, lightTheme, darkTheme } from '@adobe/react-spectrum';

function AppWrapper({ children, darkMode }) {
  const theme = useMemo(
    () => darkMode ? darkTheme : lightTheme,
    [darkMode]
  );

  return (
    <Provider theme={theme}>
      {children}
    </Provider>
  );
}
```

## Testing Themes

### Unit Testing

```jsx
import { render } from '@testing-library/react';
import { Provider, lightTheme, darkTheme } from '@adobe/react-spectrum';

function renderWithTheme(component, theme) {
  return render(
    <Provider theme={theme}>
      {component}
    </Provider>
  );
}

test('renders in light theme', () => {
  const { container } = renderWithTheme(
    <MyComponent />,
    lightTheme
  );
  expect(container).toBeInTheDocument();
});

test('renders in dark theme', () => {
  const { container } = renderWithTheme(
    <MyComponent />,
    darkTheme
  );
  expect(container).toBeInTheDocument();
});
```

### Visual Regression Testing

```jsx
// Example with Percy
import { percySnapshot } from '@percy/cli';

test('MyComponent visual regression - light', () => {
  const { container } = renderWithTheme(
    <MyComponent />,
    lightTheme
  );
  percySnapshot(container, { name: 'MyComponent Light' });
});

test('MyComponent visual regression - dark', () => {
  const { container } = renderWithTheme(
    <MyComponent />,
    darkTheme
  );
  percySnapshot(container, { name: 'MyComponent Dark' });
});
```

## Common Customization Scenarios

### Brand Color Customization
```jsx
const myBrandTheme = {
  ...lightTheme,
  colors: {
    ...lightTheme.colors,
    blue: {
      // Your brand color scale
      ...lightTheme.colors.blue,
      500: '#YOUR_BRAND_COLOR',
    },
  },
};
```

### Large Font Accessibility
```jsx
const largeTextTheme = {
  ...lightTheme,
  typography: {
    ...lightTheme.typography,
    // Increase all font sizes by 10%
  },
};
```

### Enterprise Spacing
```jsx
const compactTheme = {
  ...lightTheme,
  dimension: {
    ...lightTheme.dimension,
    size: {
      // Reduce all spacing by 25%
    },
  },
};
```

## Theming Checklist

- [ ] Test light and dark themes
- [ ] Verify color contrast (WCAG AAA - 7:1 for text)
- [ ] Test on small/medium/large screens
- [ ] Test with system dark mode preference
- [ ] Test keyboard navigation with theme
- [ ] Test focus indicators visibility
- [ ] Test with high contrast mode
- [ ] Verify RTL support if needed
- [ ] Performance test with DevTools
- [ ] Visual regression testing with both themes
