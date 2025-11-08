# React Spectrum Accessibility Patterns (WCAG 2.1 AA)

Comprehensive guide to implementing WCAG 2.1 AA compliant interfaces using React Spectrum.

## Accessibility Standards

### WCAG 2.1 Levels
- **Level A**: Basic accessibility
- **Level AA**: Enhanced accessibility (required for most organizations)
- **Level AAA**: Advanced accessibility (recommended for government/educational)

### Spectrum's Built-in Support
React Spectrum components are WCAG 2.1 AA compliant by default:
- Semantic HTML
- ARIA attributes
- Keyboard navigation
- Screen reader support
- Color contrast
- Focus management

## Form Accessibility

### Required Form Pattern

**Pattern: Always label form inputs**

```jsx
import { TextField, Text } from '@adobe/react-spectrum';

// Good: Semantic label
<TextField
  label="Email Address"
  type="email"
  placeholder="user@example.com"
  isRequired
/>

// Avoid: Missing label
<TextField
  type="email"
  placeholder="user@example.com"
/>

// Acceptable: Hidden label (aria-label)
<TextField
  aria-label="Email Address"
  type="email"
  placeholder="user@example.com"
/>
```

### Form Validation and Error Messages

**Pattern: Provide immediate validation feedback**

```jsx
import { TextField } from '@adobe/react-spectrum';
import { useState } from 'react';

function EmailField() {
  const [value, setValue] = useState('');
  const [error, setError] = useState('');

  const validateEmail = (email) => {
    const re = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
    if (!re.test(email)) {
      setError('Invalid email format');
    } else {
      setError('');
    }
  };

  return (
    <TextField
      label="Email"
      value={value}
      onChange={(val) => {
        setValue(val);
        validateEmail(val);
      }}
      validationState={error ? 'invalid' : 'valid'}
      errorMessage={error}
      help="Format: user@example.com"
      isRequired
    />
  );
}
```

### Help Text and Context

```jsx
<TextField
  label="Password"
  type="password"
  help="Minimum 8 characters, including uppercase, number, and symbol"
  validationState={passwordStrength < 3 ? 'invalid' : undefined}
  errorMessage={passwordStrength < 3 ? 'Password too weak' : undefined}
/>
```

### Radio and Checkbox Groups

**Pattern: Group with semantic fieldset**

```jsx
import { RadioGroup, Radio, Checkbox, CheckboxGroup } from '@adobe/react-spectrum';

// Good: Grouped with legend
<RadioGroup label="Preferred Contact Method">
  <Radio value="email">Email</Radio>
  <Radio value="phone">Phone</Radio>
  <Radio value="sms">SMS</Radio>
</RadioGroup>

// Good: Checkbox group
<CheckboxGroup label="Which topics interest you?">
  <Checkbox value="design">Design</Checkbox>
  <Checkbox value="development">Development</Checkbox>
  <Checkbox value="marketing">Marketing</Checkbox>
</CheckboxGroup>
```

### Select/Picker Accessibility

```jsx
import { Picker, Item } from '@adobe/react-spectrum';

<Picker label="Select Country" isRequired>
  <Item key="us">United States</Item>
  <Item key="ca">Canada</Item>
  <Item key="mx">Mexico</Item>
</Picker>
```

### Accessible Date Pickers

```jsx
import { DatePicker } from '@adobe/react-spectrum';
import { parseDate } from '@adobe/react-spectrum';

<DatePicker
  label="Start Date"
  help="Select a date between Jan 1 and Dec 31, 2024"
  minValue={parseDate('2024-01-01')}
  maxValue={parseDate('2024-12-31')}
  isRequired
/>
```

## Dialog and Modal Accessibility

### Dialog Pattern

```jsx
import {
  Dialog,
  DialogTrigger,
  Button,
  Heading,
  Content,
  Footer,
} from '@adobe/react-spectrum';

function ConfirmDialog() {
  return (
    <DialogTrigger>
      <Button>Delete Item</Button>
      <AlertDialog
        title="Confirm Deletion"
        variant="destructive"
        primaryActionLabel="Delete"
        cancelLabel="Cancel"
        onPrimaryAction={handleDelete}
      >
        This action cannot be undone. Continue?
      </AlertDialog>
    </DialogTrigger>
  );
}
```

### Focus Management in Dialogs
React Spectrum automatically:
- Moves focus to dialog on open
- Returns focus to trigger on close
- Traps keyboard focus inside dialog
- Closes on Escape key press

### Modal with Keyboard Shortcuts

```jsx
function Modal({ isOpen, onClose }) {
  useEffect(() => {
    if (!isOpen) return;

    const handleEscape = (e) => {
      if (e.key === 'Escape') {
        onClose();
      }
    };

    window.addEventListener('keydown', handleEscape);
    return () => window.removeEventListener('keydown', handleEscape);
  }, [isOpen, onClose]);

  return (
    <Dialog isDismissable>
      <Content>Dialog content</Content>
    </Dialog>
  );
}
```

## Button Accessibility

### Action Buttons (Icon-Only)

**Pattern: Always provide aria-label on icon buttons**

```jsx
import { ActionButton } from '@adobe/react-spectrum';
import { Edit, Delete, Info } from '@spectrum-icons/ui';

// Good: aria-label provided
<ActionButton aria-label="Edit item">
  <Edit />
</ActionButton>

// Avoid: Missing label
<ActionButton>
  <Edit />
</ActionButton>

// Good: With tooltip for context
<Tooltip content="Edit item">
  <ActionButton aria-label="Edit item">
    <Edit />
  </ActionButton>
</Tooltip>
```

### Button Loading States

```jsx
import { Button } from '@adobe/react-spectrum';

function SubmitButton({ isLoading, isDisabled }) {
  return (
    <Button
      variant="cta"
      isDisabled={isLoading || isDisabled}
      onPress={handleSubmit}
    >
      {isLoading ? 'Loading...' : 'Submit'}
    </Button>
  );
}
```

## Keyboard Navigation

### Tab Order Management

```jsx
import { Flex, TextField, Button } from '@adobe/react-spectrum';
import { useRef } from 'react';

function FormWithCustomOrder() {
  const nameRef = useRef();
  const emailRef = useRef();

  return (
    <Flex direction="column" gap="size-200">
      <TextField
        ref={nameRef}
        label="Name"
        tabIndex={1}
      />
      <TextField
        ref={emailRef}
        label="Email"
        tabIndex={2}
      />
      <Button tabIndex={3}>Submit</Button>
    </Flex>
  );
}
```

### Escape Key Handling

```jsx
import { Dialog } from '@adobe/react-spectrum';

<Dialog isDismissable onClose={handleClose}>
  {/* Escape automatically closes dialog */}
  Content
</Dialog>
```

### Arrow Key Navigation

```jsx
import { Menu, Item } from '@adobe/react-spectrum';

<Menu onAction={handleSelection}>
  {/* Arrow keys navigate items */}
  <Item key="one">Option One</Item>
  <Item key="two">Option Two</Item>
</Menu>
```

## Screen Reader Support

### Live Regions for Updates

```jsx
import { useState } from 'react';
import { Button } from '@adobe/react-spectrum';

function DynamicContent() {
  const [message, setMessage] = useState('');

  return (
    <>
      <Button onPress={() => setMessage('Action completed!')}>
        Perform Action
      </Button>

      <div role="status" aria-live="polite" aria-atomic="true">
        {message}
      </div>
    </>
  );
}
```

### Progress Announcements

```jsx
function UploadProgress({ progress }) {
  return (
    <>
      <ProgressBar
        value={progress}
        maxValue={100}
        label="Upload progress"
        aria-label={`Upload ${progress}% complete`}
      />
      <div
        role="status"
        aria-live="assertive"
        aria-atomic="true"
      >
        {progress === 100 ? 'Upload complete' : `Uploading: ${progress}%`}
      </div>
    </>
  );
}
```

### Form Errors Announcement

```jsx
import { TextField, Text } from '@adobe/react-spectrum';

function FieldWithAnnouncement({ value, error }) {
  return (
    <>
      <TextField
        label="Username"
        value={value}
        validationState={error ? 'invalid' : undefined}
        errorMessage={error}
        aria-describedby={error ? 'error-message' : undefined}
      />
      {error && (
        <Text role="alert" id="error-message" color="negative">
          {error}
        </Text>
      )}
    </>
  );
}
```

## Color Contrast

### WCAG AAA Standards
- Normal text: 7:1 ratio (minimum)
- Large text (18pt+): 4.5:1 ratio (minimum)

### Testing Contrast

```jsx
// Use contrast checker tools
// Online: https://www.tpgi.com/color-contrast-checker/
// Command line: pa11y, axe, lighthouse

// Spectrum ensures AA/AAA compliance in:
// - Light theme: Dark text on light backgrounds
// - Dark theme: Light text on dark backgrounds
// - Disabled states: Reduced but sufficient contrast

// Test in both themes
<Provider theme={lightTheme}>
  <MyComponent />
</Provider>

<Provider theme={darkTheme}>
  <MyComponent />
</Provider>
```

## Focus Indicators

### Never Remove Focus Rings

```jsx
// Good: Default focus behavior (preserved)
<Button onPress={handleClick}>Click me</Button>

// Avoid: Removing focus indicator
const styles = `
  button:focus {
    outline: none;  /* BAD: Removes keyboard focus indicator */
  }
`;

// If styling focus, always provide visible indicator:
const styles = `
  button:focus {
    outline: 3px solid #0078d4;
    outline-offset: 2px;
  }
`;
```

### Focus Visible Pseudo-class

```jsx
// Use :focus-visible for keyboard-only focus
const focusStyle = `
  button:focus-visible {
    outline: 3px solid #0078d4;
    outline-offset: 2px;
  }
`;
```

## Text Alternatives

### Images and Icons

```jsx
import { Icon, Image } from '@adobe/react-spectrum';
import { Info } from '@spectrum-icons/ui';

// Icon with aria-label
<Icon aria-label="Information">
  <Info />
</Icon>

// Tooltip for context
<Tooltip content="Help information">
  <Icon aria-label="Information">
    <Info />
  </Icon>
</Tooltip>

// Image with alt text
<Image
  src="chart.png"
  alt="Monthly sales chart showing 25% growth"
/>
```

## Complex Table Accessibility

```jsx
import { Table, Column, Row, Cell } from '@adobe/react-spectrum';

function AccessibleTable() {
  return (
    <Table
      aria-label="Employee directory with sortable columns"
      selectedKeys={selected}
      onSelectionChange={setSelected}
    >
      <TableHeader>
        <Column key="name" allowsSorting>
          Name
        </Column>
        <Column key="role" allowsSorting>
          Job Title
        </Column>
        <Column key="email">
          Email
        </Column>
      </TableHeader>
      <TableBody>
        {employees.map(emp => (
          <Row key={emp.id}>
            <Cell>{emp.name}</Cell>
            <Cell>{emp.role}</Cell>
            <Cell>
              <Link href={`mailto:${emp.email}`}>
                {emp.email}
              </Link>
            </Cell>
          </Row>
        ))}
      </TableBody>
    </Table>
  );
}
```

## Accessible Lists

```jsx
import { ListBox, Item } from '@adobe/react-spectrum';

<ListBox
  aria-label="Display options"
  selectedKey={view}
  onSelectionChange={setView}
>
  <Item key="list" textValue="List view">
    List View
  </Item>
  <Item key="grid" textValue="Grid view">
    Grid View
  </Item>
  <Item key="table" textValue="Table view">
    Table View
  </Item>
</ListBox>
```

## Test Checklist

### Automated Testing
- [ ] Run axe DevTools and fix violations
- [ ] Run WAVE browser extension
- [ ] Run Lighthouse accessibility audit
- [ ] Run pa11y CLI for batch testing

### Manual Testing

**Keyboard Navigation:**
- [ ] Tab through all interactive elements
- [ ] All functionality accessible via keyboard
- [ ] Logical tab order
- [ ] Focus indicators visible
- [ ] Escape closes dialogs/popovers
- [ ] Arrow keys work in lists/menus

**Screen Reader (NVDA/JAWS/VoiceOver):**
- [ ] All form inputs labeled
- [ ] Error messages announced
- [ ] Status updates announced
- [ ] Dialog announced as modal
- [ ] Table headers associated with cells
- [ ] Page structure logical

**Visual:**
- [ ] Color contrast sufficient (7:1 for text)
- [ ] Text resizable to 200% without scrolling
- [ ] No seizure-triggering animations (>3 flashes/second)
- [ ] Motion not required for functionality

**Cognitive:**
- [ ] Plain language used
- [ ] Instructions clear and simple
- [ ] Error recovery options available
- [ ] Consistent navigation

## Performance Impact of Accessibility

Spectrum's accessibility features have minimal performance impact:
- Native semantics (fast)
- CSS-based indicators (no JavaScript overhead)
- Efficient ARIA (only when needed)
- Built-in focus management

### Monitor with DevTools

```jsx
// Check accessibility tree in DevTools
// Firefox: Inspector > Accessibility tab
// Chrome: DevTools > Lighthouse tab

// Performance: Should not impact FCP/LCP
// Use React DevTools Profiler to verify
```

## Resources for Further Learning

- [WCAG 2.1 Guidelines](https://www.w3.org/WAI/WCAG21/quickref/)
- [ARIA Authoring Practices](https://www.w3.org/WAI/ARIA/apg/)
- [React Spectrum Accessibility](https://react-spectrum.adobe.com/docs/concepts/accessibility.html)
- [WebAIM Articles](https://webaim.org/articles/)
- [A11y Project](https://www.a11yproject.com/)

## Accessibility Principles (from W3C)

1. **Perceivable**: Information presented in ways users can perceive
2. **Operable**: Functionality operable through keyboard and other inputs
3. **Understandable**: Information and operations understandable
4. **Robust**: Compatible with current and future assistive technologies

All Spectrum components are built with these principles in mind.
