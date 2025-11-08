---
name: adobe-react-spectrum-design
description: Implement professional Adobe-style UI with React Spectrum v3.45.0. Use when building accessible UI components, implementing dark mode, creating professional creative tool aesthetics, ensuring WCAG 2.1 AA compliance, or designing desktop application interfaces.
---

# Adobe React Spectrum Design System

## Overview

React Spectrum is Adobe's design system and component library providing a comprehensive set of pre-built, accessible components designed for professional applications. Built with React and TypeScript, it delivers enterprise-grade UI patterns with full accessibility support out of the box, making it ideal for desktop applications, creative tools, and enterprise interfaces.

## When to Use React Spectrum

### Ideal For:
- Building desktop application UIs (Electron, Tauri, etc.)
- Creating professional creative tools and content management systems
- Enterprise dashboard and admin interfaces
- Applications requiring WCAG 2.1 AA compliance
- Multi-theme/white-label applications
- Teams prioritizing accessibility
- Complex form-heavy applications
- Projects requiring consistent design at scale

### Not Ideal For:
- Lightweight marketing websites (consider headless alternatives)
- Minimalist consumer apps (might be over-featured)
- Projects with highly custom design requirements conflicting with Spectrum aesthetic

## Component Categories and Usage

### Layout Components
The foundation for building responsive, accessible layouts with flexbox and grid systems.

**Common Components:**
- `Flex`: Flexible box layout with comprehensive spacing/alignment
- `Grid`: CSS Grid-based layouts
- `View`: Base container with padding and dimensions
- `VStack/HStack`: Semantic vertical/horizontal stacking
- `Spacer`: Responsive spacing utility

**Example:**
```jsx
import { Flex, Button, Text } from '@adobe/react-spectrum';

<Flex gap="size-200" direction="column">
  <Text>Title</Text>
  <Button variant="cta">Action</Button>
</Flex>
```

### Form Components
Complete form building with validation, error handling, and accessibility built-in.

**Common Components:**
- `TextField`: Text input with validation, icons, help text
- `TextArea`: Multi-line text input
- `NumberField`: Number input with increment/decrement
- `Checkbox`: Single/group checkbox selection
- `Radio`: Radio button groups
- `Picker`: Dropdown select component
- `ComboBox`: Searchable select with custom values
- `DatePicker`: Date selection with calendar
- `Slider`: Range/value sliders
- `Switch`: Toggle on/off states

**Example:**
```jsx
import { TextField, NumberField, Checkbox } from '@adobe/react-spectrum';

<TextField
  label="Full Name"
  placeholder="Enter your name"
  validationState={hasError ? "invalid" : undefined}
  errorMessage="Name is required"
/>
```

### Action Components
Components for user interactions and navigation.

**Common Components:**
- `Button`: Primary/secondary/tertiary action buttons
- `Link`: Styled hyperlinks
- `Menu`: Dropdown action menus
- `ActionButton`: Icon-only action buttons
- `LogicButton`: Toggle/state buttons

**Example:**
```jsx
import { Button, ActionButton } from '@adobe/react-spectrum';
import { Edit } from '@spectrum-icons/ui';

<Button variant="cta" onPress={handleSubmit}>
  Submit
</Button>
<ActionButton aria-label="Edit"><Edit /></ActionButton>
```

### Display Components
Components for presenting information and status.

**Common Components:**
- `Badge`: Status/count indicators
- `Tag`: Categorical labels
- `Avatar`: User profile images
- `Icon`: SVG icon system (1200+ icons)
- `StatusLight`: Status indicators
- `ProgressBar`: Progress visualization
- `Meter`: Measurement display

### Dialog and Overlay Components
Modal and floating content for focused interactions.

**Common Components:**
- `Dialog/AlertDialog`: Modal dialogs
- `Popover`: Floating content containers
- `Tooltip`: Hover/focus hint text
- `Breadcrumbs`: Navigation hierarchy

**Example:**
```jsx
import { Dialog, DialogTrigger, Button, Heading, Content } from '@adobe/react-spectrum';

<DialogTrigger>
  <Button>Open Dialog</Button>
  <Dialog>
    <Heading>Confirm Action</Heading>
    <Content>Are you sure?</Content>
  </Dialog>
</DialogTrigger>
```

### Data Display Components
Components for rendering collections and complex data.

**Common Components:**
- `Table`: Complex data tables with sorting/filtering
- `List/ListBox`: Item collection selection
- `Tabs`: Tabbed content organization
- `Accordion`: Collapsible content sections

## Theming and Customization

React Spectrum provides a robust theming system built on CSS variables (custom properties), enabling full customization while maintaining design consistency.

### Theme Properties
- **Color Scales**: 12-step perceptual color scales for each color
- **Typography**: Font sizes, weights, line heights
- **Spacing**: Base unit (8px) with 13-step scale
- **Border Radius**: Consistent corner rounding
- **Shadows**: Elevation shadows system
- **Opacity**: Alpha channel scales
- **Animation**: Timing and easing functions

### Implementation Approaches

**1. Using Preset Themes:**
```jsx
import { Provider } from '@adobe/react-spectrum';
import { lightTheme, darkTheme } from '@adobe/react-spectrum';

<Provider theme={lightTheme}>
  <App />
</Provider>
```

**2. Creating Custom Themes:**
See `spectrum-theme-template.ts` in assets for starter template structure.

**3. CSS Variable Overrides:**
```css
:root {
  --spectrum-global-color-blue-500: #0078d4;
  --spectrum-global-dimension-size-200: 16px;
}
```

## Dark Mode Implementation

React Spectrum's dark mode leverages perceptual color matching—colors maintain visual hierarchy and readability across themes.

### Setup
```jsx
import { Provider } from '@adobe/react-spectrum';
import { darkTheme } from '@adobe/react-spectrum';

<Provider theme={darkTheme}>
  <App />
</Provider>
```

### System Preference Detection
```jsx
import { useColorScheme } from '@adobe/react-spectrum';

function App() {
  const colorScheme = useColorScheme();
  return <div>{colorScheme === 'dark' ? 'Dark' : 'Light'}</div>;
}
```

### Best Practices
- Never hardcode colors; use semantic tokens
- Test contrast ratios in both themes (aim for WCAG AAA 7:1)
- Use theme-aware logic for non-color styling
- Provide user preference toggle in settings

## Accessibility Patterns (WCAG 2.1 AA)

### Core Principles
- **Semantic HTML**: Proper ARIA labels and roles
- **Keyboard Navigation**: Tab order, arrow keys, Enter/Escape
- **Screen Reader Support**: Announcements and live regions
- **Color Contrast**: WCAG AAA standards (7:1 for text, 4.5:1 minimum)
- **Focus Management**: Clear visible focus indicators (never remove!)

### Form Validation Pattern
```jsx
<TextField
  label="Email"
  type="email"
  validationState={hasError ? "invalid" : "valid"}
  errorMessage="Invalid email format"
  isRequired
/>
```

### Loading States
```jsx
<Button isDisabled={isLoading}>
  {isLoading ? 'Loading...' : 'Submit'}
</Button>
```

### Dynamic Content Announcements
```jsx
<div role="status" aria-live="polite" aria-atomic="true">
  {statusMessage}
</div>
```

### Keyboard Navigation Example
```jsx
<Menu onAction={handleSelection}>
  <Item key="edit">Edit</Item>
  <Item key="delete">Delete</Item>
</Menu>
```

### Testing Accessibility
- Use `spectrum-audit.py` for automated component analysis
- Manual keyboard-only testing
- Screen reader testing (NVDA, JAWS, VoiceOver)
- Color contrast verification (WebAIM, axe DevTools)
- See `accessibility-patterns.md` for comprehensive patterns

## Layout System and Responsive Design

React Spectrum's layout system combines flexbox, grid, and CSS logical properties for responsive, RTL-friendly layouts.

### Responsive Sizing
```jsx
<View width={{ base: '100%', M: '50%', L: '33%' }} />
```

**Breakpoints:**
- `base`: 0px
- `S`: 640px
- `M`: 768px
- `L`: 1024px
- `XL`: 1280px

### Spacing Scale (8px base unit)
- `size-50`: 4px
- `size-100`: 8px
- `size-200`: 16px
- `size-300`: 24px
- `size-400`: 32px
- Scale continues up to `size-3200`: 3200px

### Alignment Primitives
```jsx
<Flex
  alignItems="center"
  justifyContent="space-between"
  gap="size-200"
>
  {children}
</Flex>
```

## React Integration and Setup

### Installation
```bash
npm install @adobe/react-spectrum @adobe/react-spectrum-icons @spectrum-icons/ui
```

### Basic Application Setup
```jsx
import { Provider, Button, Text } from '@adobe/react-spectrum';
import { lightTheme } from '@adobe/react-spectrum';

export function App() {
  return (
    <Provider theme={lightTheme} locale="en-US">
      <Button variant="cta">Get Started</Button>
    </Provider>
  );
}
```

### Integration with Form Libraries
```jsx
import { useController } from 'react-hook-form';
import { TextField } from '@adobe/react-spectrum';

function MyField({ control, name }) {
  const { field, fieldState } = useController({
    control,
    name,
  });

  return (
    <TextField
      {...field}
      value={field.value || ''}
      validationState={fieldState.error ? 'invalid' : undefined}
      errorMessage={fieldState.error?.message}
    />
  );
}
```

### Performance Considerations
- Use virtualization for large lists (100+ items)
- Memoize complex component rendering with `React.memo()`
- Lazy load heavy dialog/modal components
- Correctly set `key` props on collection items
- Consider pagination for large datasets

## Resources and Documentation

This skill includes comprehensive bundled resources:

### scripts/
- `spectrum-audit.py` - Automated component usage and accessibility audit tool

### references/
- `spectrum-components-catalog.md` - Complete reference for all 40+ components
- `spectrum-theming-guide.md` - Deep dive into customization and theme creation
- `accessibility-patterns.md` - WCAG 2.1 AA compliance patterns and testing strategies

### assets/
- `spectrum-theme-template.ts` - TypeScript starter template for custom theme creation

## External References

- [React Spectrum Official Documentation](https://react-spectrum.adobe.com/)
- [WCAG 2.1 Guidelines](https://www.w3.org/WAI/WCAG21/quickref/)
- [Adobe Design System](https://spectrum.adobe.com/)
- [React Spectrum GitHub](https://github.com/adobe/react-spectrum)
