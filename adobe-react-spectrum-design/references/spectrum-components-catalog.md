# React Spectrum Components Catalog (v3.45.0)

Complete reference for all 40+ components in React Spectrum.

## Form Components

### TextField
Text input for single-line text entry.

**Props:**
- `label` (string, required): Display label
- `value` (string): Current value
- `onChange` (function): Change handler
- `validationState` ('valid' | 'invalid'): Validation state
- `errorMessage` (string): Error text
- `isRequired` (boolean): Required field indicator
- `isDisabled` (boolean): Disabled state
- `type` (string): Input type ('text', 'email', 'password', etc.)
- `placeholder` (string): Placeholder text
- `icon` (component): Left icon
- `help` (string): Help text below input

**Example:**
```jsx
<TextField
  label="Email"
  type="email"
  placeholder="user@example.com"
  validationState={hasError ? 'invalid' : undefined}
  errorMessage="Invalid email format"
  help="We'll never share your email"
  isRequired
/>
```

### TextArea
Multi-line text input.

**Props:**
- `label` (string, required)
- `value` (string)
- `onChange` (function)
- `validationState` ('valid' | 'invalid')
- `errorMessage` (string)
- `placeholder` (string)
- `isRequired` (boolean)
- `isDisabled` (boolean)

**Example:**
```jsx
<TextArea
  label="Comments"
  placeholder="Enter your feedback..."
  rows={6}
  maxLength={500}
/>
```

### NumberField
Number input with increment/decrement controls.

**Props:**
- `label` (string, required)
- `value` (number)
- `onChange` (function)
- `minValue` (number): Minimum value
- `maxValue` (number): Maximum value
- `step` (number): Increment step
- `formatOptions` (object): Number formatting

**Example:**
```jsx
<NumberField
  label="Quantity"
  minValue={1}
  maxValue={100}
  step={1}
  defaultValue={5}
/>
```

### Checkbox
Single checkbox or group of checkboxes.

**Props:**
- `value` (string, required)
- `isSelected` (boolean)
- `onChange` (function)
- `isIndeterminate` (boolean): Tri-state
- `isDisabled` (boolean)
- `children` (string): Label text

**Example:**
```jsx
<Checkbox value="agree" onChange={setAgree}>
  I agree to the terms
</Checkbox>
```

### CheckboxGroup
Container for multiple checkboxes.

**Props:**
- `label` (string)
- `value` (string[])
- `onChange` (function)
- `validationState` ('valid' | 'invalid')
- `children` (elements): Checkbox items

**Example:**
```jsx
<CheckboxGroup label="Preferences" value={selected}>
  <Checkbox value="email">Email notifications</Checkbox>
  <Checkbox value="sms">SMS notifications</Checkbox>
</CheckboxGroup>
```

### Radio / RadioGroup
Single or grouped radio buttons.

**Props:**
- `value` (string)
- `isSelected` (boolean)
- `onChange` (function)
- `isDisabled` (boolean)
- `children` (string): Label

**Example:**
```jsx
<RadioGroup label="Theme" value={theme} onChange={setTheme}>
  <Radio value="light">Light</Radio>
  <Radio value="dark">Dark</Radio>
  <Radio value="auto">Auto</Radio>
</RadioGroup>
```

### Switch
Toggle on/off control.

**Props:**
- `isSelected` (boolean)
- `onChange` (function)
- `isDisabled` (boolean)
- `children` (string): Label
- `value` (string): Form value

**Example:**
```jsx
<Switch isSelected={darkMode} onChange={setDarkMode}>
  Dark Mode
</Switch>
```

### Slider / RangeSlider
Single or range value selection.

**Props:**
- `label` (string)
- `value` (number | [number, number])
- `onChange` (function)
- `minValue` (number)
- `maxValue` (number)
- `step` (number)
- `getValueLabel` (function): Custom labels

**Example:**
```jsx
<RangeSlider
  label="Price Range"
  minValue={0}
  maxValue={1000}
  step={50}
  defaultValue={[100, 500]}
/>
```

### DatePicker
Calendar-based date selection.

**Props:**
- `label` (string)
- `value` (Date | CalendarDate)
- `onChange` (function)
- `minValue` (Date)
- `maxValue` (Date)
- `isDisabled` (boolean)
- `formatOptions` (object): Date format

**Example:**
```jsx
<DatePicker
  label="Start Date"
  defaultValue={parseDate('2024-01-01')}
  minValue={parseDate('2024-01-01')}
  maxValue={parseDate('2024-12-31')}
/>
```

### DateRangePicker
Select date range with two calendars.

**Props:**
- `label` (string)
- `value` (RangeValue<CalendarDate>)
- `onChange` (function)
- `minValue` (Date)
- `maxValue` (Date)

**Example:**
```jsx
<DateRangePicker
  label="Date Range"
  defaultValue={{
    start: parseDate('2024-01-01'),
    end: parseDate('2024-01-31'),
  }}
/>
```

### Picker
Dropdown select component.

**Props:**
- `label` (string)
- `items` (array): Collection items
- `selectedKey` (string | number)
- `onSelectionChange` (function)
- `isDisabled` (boolean)
- `isRequired` (boolean)
- `errorMessage` (string)
- `children` (elements): Item elements

**Example:**
```jsx
<Picker label="Select Country">
  <Item key="us">United States</Item>
  <Item key="ca">Canada</Item>
  <Item key="mx">Mexico</Item>
</Picker>
```

### ComboBox
Searchable select with custom value support.

**Props:**
- `label` (string)
- `items` (array)
- `selectedKey` (string | number)
- `onSelectionChange` (function)
- `inputValue` (string)
- `onInputChange` (function)
- `allowsCustomValue` (boolean)
- `isDisabled` (boolean)
- `children` (elements): Item elements

**Example:**
```jsx
<ComboBox label="Programming Language" allowsCustomValue>
  <Item key="js">JavaScript</Item>
  <Item key="py">Python</Item>
  <Item key="rust">Rust</Item>
</ComboBox>
```

### SearchField
Specialized input for search queries.

**Props:**
- `label` (string)
- `value` (string)
- `onChange` (function)
- `onSubmit` (function)
- `onClear` (function)
- `placeholder` (string)
- `isDisabled` (boolean)
- `icon` (component): Search icon

**Example:**
```jsx
<SearchField
  label="Search"
  placeholder="Search products..."
  onSubmit={handleSearch}
/>
```

## Button Components

### Button
Primary action button.

**Props:**
- `onPress` (function): Click handler
- `variant` ('cta' | 'primary' | 'secondary' | 'accent' | 'negative'): Style variant
- `size` ('S' | 'M' | 'L'): Button size
- `isDisabled` (boolean): Disabled state
- `isLoading` (boolean): Loading state
- `type` ('button' | 'submit' | 'reset'): Form type
- `children` (string | elements): Button content

**Example:**
```jsx
<Button
  variant="cta"
  size="L"
  onPress={handleSubmit}
  isDisabled={isLoading}
>
  {isLoading ? 'Loading...' : 'Submit'}
</Button>
```

### ActionButton
Icon-only button for compact layouts.

**Props:**
- `onPress` (function)
- `isDisabled` (boolean)
- `aria-label` (string, required): Accessibility label
- `children` (element): Icon component

**Example:**
```jsx
<ActionButton aria-label="Edit item">
  <Edit />
</ActionButton>
```

### Link
Styled hyperlink.

**Props:**
- `href` (string): Link target
- `target` (string): Link target window
- `variant` ('primary' | 'secondary'): Style
- `isDisabled` (boolean)
- `children` (string | elements): Link content

**Example:**
```jsx
<Link href="https://example.com" target="_blank">
  Learn More
</Link>
```

## Dialog Components

### Dialog / AlertDialog
Modal dialogs for focused interactions.

**Props:**
- `isDismissable` (boolean): Can close via escape/backdrop click
- `onClose` (function): Close handler
- `children` (elements): Content elements

**Example:**
```jsx
<DialogTrigger>
  <Button>Open Dialog</Button>
  <AlertDialog
    title="Confirm Delete"
    primaryActionLabel="Delete"
    cancelLabel="Cancel"
    onPrimaryAction={handleDelete}
  >
    This action cannot be undone.
  </AlertDialog>
</DialogTrigger>
```

### Popover
Floating panel attached to a trigger.

**Props:**
- `placement` ('start' | 'end' | 'top' | 'bottom'): Position
- `offset` (number): Pixel offset
- `shouldFlip` (boolean): Flip if no space
- `onClose` (function): Close handler
- `children` (elements): Content

**Example:**
```jsx
<PopoverTrigger>
  <ActionButton>More</ActionButton>
  <Popover>
    <Menu>
      <Item key="edit">Edit</Item>
      <Item key="delete">Delete</Item>
    </Menu>
  </Popover>
</PopoverTrigger>
```

### Tooltip
Hover/focus hint text.

**Props:**
- `isOpen` (boolean): Visibility
- `isDisabled` (boolean)
- `delay` (number): Show delay in ms
- `children` (elements): Trigger element
- `content` (string): Tooltip text

**Example:**
```jsx
<Tooltip content="Click to refresh" delay={100}>
  <ActionButton>
    <Refresh />
  </ActionButton>
</Tooltip>
```

### Breadcrumbs
Navigation hierarchy.

**Props:**
- `items` (array): Breadcrumb items
- `onAction` (function): Item click handler
- `isDisabled` (boolean)
- `children` (elements): Item elements

**Example:**
```jsx
<Breadcrumbs>
  <Item key="home">Home</Item>
  <Item key="docs">Documentation</Item>
  <Item key="api">API Reference</Item>
</Breadcrumbs>
```

## Data Display Components

### Table
Complex data tables with sorting and selection.

**Props:**
- `aria-label` (string)
- `selectedKeys` (string[] | 'all')
- `onSelectionChange` (function)
- `sortDescriptor` (object): Sort state
- `onSortChange` (function)
- `children` (elements): Columns and rows

**Example:**
```jsx
<Table>
  <TableHeader>
    <Column key="name" allowsSorting>Name</Column>
    <Column key="email">Email</Column>
  </TableHeader>
  <TableBody>
    {users.map(user => (
      <Row key={user.id}>
        <Cell>{user.name}</Cell>
        <Cell>{user.email}</Cell>
      </Row>
    ))}
  </TableBody>
</Table>
```

### List / ListBox
Item collection selection.

**Props:**
- `items` (array)
- `selectedKeys` (string | string[] | 'all')
- `onSelectionChange` (function)
- `selectionMode` ('single' | 'multiple' | 'none'): Selection type
- `isDisabled` (boolean)
- `children` (elements): Item elements

**Example:**
```jsx
<ListBox selectedKey={selected} onSelectionChange={setSelected}>
  <Item key="list">List View</Item>
  <Item key="grid">Grid View</Item>
  <Item key="table">Table View</Item>
</ListBox>
```

### Tabs
Tabbed content organization.

**Props:**
- `selectedKey` (string)
- `onSelectionChange` (function)
- `isDisabled` (boolean)
- `orientation` ('horizontal' | 'vertical'): Tab layout
- `children` (elements): Tab and panel pairs

**Example:**
```jsx
<Tabs selectedKey={tab} onSelectionChange={setTab}>
  <TabList>
    <Item key="settings">Settings</Item>
    <Item key="advanced">Advanced</Item>
  </TabList>
  <TabPanels>
    <Item key="settings">Settings content</Item>
    <Item key="advanced">Advanced content</Item>
  </TabPanels>
</Tabs>
```

### Accordion
Collapsible content sections.

**Props:**
- `selectedKey` (string)
- `onSelectionChange` (function)
- `isDisabled` (boolean)
- `children` (elements): Accordion items

**Example:**
```jsx
<Accordion>
  <Item key="general" title="General">
    General settings content
  </Item>
  <Item key="appearance" title="Appearance">
    Appearance settings content
  </Item>
</Accordion>
```

### StatusLight
Status indicator with semantic colors.

**Props:**
- `variant` ('positive' | 'notice' | 'negative' | 'info'): Status type
- `children` (string): Status label

**Example:**
```jsx
<StatusLight variant="positive">
  Approved
</StatusLight>
```

### ProgressBar / Meter
Progress and measurement visualization.

**Props:**
- `label` (string)
- `value` (number)
- `minValue` (number)
- `maxValue` (number)
- `variant` ('positive' | 'notice' | 'negative'): Color variant
- `labelPosition` ('top' | 'side'): Label placement

**Example:**
```jsx
<ProgressBar
  label="Upload Progress"
  value={uploadProgress}
  maxValue={100}
/>
```

## Display Components

### Text / Heading
Text and heading typography.

**Props:**
- `elementType` (string): HTML element ('p', 'span', etc.)
- `size` (string): Font size scale
- `weight` (string): Font weight ('thin' to 'bold')
- `color` (string): Semantic color token
- `children` (string | elements): Content

**Example:**
```jsx
<Heading level={2} size="L">
  Section Title
</Heading>

<Text size="M" weight="semibold">
  Regular text content
</Text>
```

### Badge / Tag
Status indicators and categorical labels.

**Props:**
- `variant` ('positive' | 'notice' | 'negative' | 'info'): Color variant
- `children` (string): Content

**Example:**
```jsx
<Badge variant="positive">New</Badge>
<Tag variant="info">JavaScript</Tag>
```

### Avatar
User profile image.

**Props:**
- `src` (string): Image source
- `alt` (string): Alt text
- `size` ('S' | 'M' | 'L'): Avatar size

**Example:**
```jsx
<Avatar src="/avatar.jpg" alt="User name" size="M" />
```

### Icon
Spectrum icon system (1200+ icons).

**Props:**
- `size` ('XXS' | 'XS' | 'S' | 'M' | 'L' | 'XL' | 'XXL'): Icon size
- `color` (string): Semantic color token
- `aria-label` (string): Accessibility label

**Example:**
```jsx
import { Edit, Delete, Info } from '@spectrum-icons/ui';

<Edit size="M" />
<Delete size="L" color="negative" />
<Info aria-label="Information" />
```

## Layout Components

### Flex
Flexible box layout container.

**Props:**
- `direction` ('row' | 'column' | 'row-reverse' | 'column-reverse'): Flex direction
- `gap` (string): Space between items (Spectrum size token)
- `alignItems` ('flex-start' | 'center' | 'flex-end' | 'stretch'): Alignment
- `justifyContent` ('flex-start' | 'center' | 'flex-end' | 'space-between' | 'space-around'): Justification
- `wrap` ('wrap' | 'nowrap'): Wrapping behavior
- `children` (elements): Container content

**Example:**
```jsx
<Flex direction="row" gap="size-200" alignItems="center">
  <Icon size="L" />
  <Text>Item</Text>
</Flex>
```

### Grid
CSS Grid layout container.

**Props:**
- `columns` (string | string[]): Grid columns (CSS grid string or responsive)
- `gap` (string): Space between items
- `columnGap` (string): Column gap only
- `rowGap` (string): Row gap only
- `autoFlow` ('row' | 'column' | 'dense'): Auto-flow direction
- `children` (elements): Grid items

**Example:**
```jsx
<Grid columns={['1fr', '1fr']} gap="size-200">
  <Item>Item 1</Item>
  <Item>Item 2</Item>
</Grid>
```

### View
Base container component.

**Props:**
- `padding` (string): Padding (Spectrum size token)
- `paddingX` (string): Horizontal padding
- `paddingY` (string): Vertical padding
- `width` (string | object): Width (responsive)
- `height` (string): Height
- `borderRadius` (string): Border radius token
- `backgroundColor` (string): Background color token
- `children` (elements): Content

**Example:**
```jsx
<View padding="size-300" borderRadius="medium" backgroundColor="gray-50">
  Content
</View>
```

### VStack / HStack
Semantic vertical/horizontal stacking.

**Props:**
- `gap` (string): Space between items
- `alignItems` (string): Alignment
- `justifyContent` (string): Justification
- `children` (elements): Items

**Example:**
```jsx
<VStack gap="size-200">
  <Heading>Title</Heading>
  <Text>Description</Text>
</VStack>
```

### Spacer
Fixed spacing utility.

**Props:**
- `size` (string): Space size (Spectrum token)
- `flex` (boolean): Fill available space

**Example:**
```jsx
<Flex>
  <Text>Left</Text>
  <Spacer flex />
  <Text>Right</Text>
</Flex>
```

## Provider

### Provider
Application root provider for theme and locale.

**Props:**
- `theme` (object): Theme object (lightTheme, darkTheme, custom)
- `locale` (string): Locale code ('en-US', 'fr-FR', etc.)
- `colorScheme` ('light' | 'dark'): Force color scheme
- `children` (elements): App content

**Example:**
```jsx
import { Provider, lightTheme } from '@adobe/react-spectrum';

<Provider theme={lightTheme} locale="en-US">
  <App />
</Provider>
```

## Component Composition Best Practices

1. **Always use label prop on form inputs** for accessibility
2. **Use validationState and errorMessage** for form feedback
3. **Set aria-label on ActionButton** (icon-only buttons)
4. **Use semantic size tokens** (size-100, size-200, etc.)
5. **Use color variants** instead of hardcoding colors
6. **Test keyboard navigation** on all interactive components
7. **Consider loading/disabled states** in async operations
8. **Use semantic HTML elements** via elementType prop when needed
