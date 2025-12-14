# Gutenberg Components Reference

## Block Editor Components

Import from `@wordpress/block-editor`:

### useBlockProps

```javascript
import { useBlockProps } from '@wordpress/block-editor';

// Edit component
const blockProps = useBlockProps( {
    className: 'custom-class',
    style: { backgroundColor: 'red' },
} );
return <div { ...blockProps }>Content</div>;

// Save component
const blockProps = useBlockProps.save( {
    className: 'custom-class',
} );
return <div { ...blockProps }>Content</div>;
```

### RichText

```javascript
import { RichText } from '@wordpress/block-editor';

// Edit
<RichText
    tagName="p"
    value={ content }
    onChange={ ( value ) => setAttributes( { content: value } ) }
    placeholder="Enter text..."
    allowedFormats={ [ 'core/bold', 'core/italic', 'core/link' ] }
    multiline={ false }
    withoutInteractiveFormatting={ false }
/>

// Save
<RichText.Content tagName="p" value={ content } />
```

### InspectorControls

```javascript
import { InspectorControls } from '@wordpress/block-editor';
import { PanelBody } from '@wordpress/components';

<InspectorControls>
    <PanelBody title="Settings" initialOpen={ true }>
        {/* Controls here */}
    </PanelBody>
</InspectorControls>
```

### BlockControls

```javascript
import {
    BlockControls,
    AlignmentToolbar,
    BlockAlignmentToolbar,
} from '@wordpress/block-editor';
import { ToolbarGroup, ToolbarButton } from '@wordpress/components';

<BlockControls>
    <AlignmentToolbar
        value={ textAlign }
        onChange={ ( value ) => setAttributes( { textAlign: value } ) }
    />
    <BlockAlignmentToolbar
        value={ align }
        onChange={ ( value ) => setAttributes( { align: value } ) }
        controls={ [ 'left', 'center', 'right', 'wide', 'full' ] }
    />
    <ToolbarGroup>
        <ToolbarButton
            icon="edit"
            label="Edit"
            onClick={ () => setIsEditing( true ) }
        />
    </ToolbarGroup>
</BlockControls>
```

### MediaUpload

```javascript
import { MediaUpload, MediaUploadCheck } from '@wordpress/block-editor';
import { Button } from '@wordpress/components';

<MediaUploadCheck>
    <MediaUpload
        onSelect={ ( media ) => setAttributes( {
            mediaId: media.id,
            mediaUrl: media.url,
            mediaAlt: media.alt,
        } ) }
        allowedTypes={ [ 'image' ] }
        value={ mediaId }
        render={ ( { open } ) => (
            <Button onClick={ open } variant="secondary">
                { mediaUrl ? 'Replace Image' : 'Select Image' }
            </Button>
        ) }
    />
</MediaUploadCheck>
```

### PanelColorSettings

```javascript
import { PanelColorSettings } from '@wordpress/block-editor';

<InspectorControls>
    <PanelColorSettings
        title="Color Settings"
        colorSettings={ [
            {
                value: backgroundColor,
                onChange: ( value ) => setAttributes( { backgroundColor: value } ),
                label: 'Background Color',
            },
            {
                value: textColor,
                onChange: ( value ) => setAttributes( { textColor: value } ),
                label: 'Text Color',
            },
        ] }
    />
</InspectorControls>
```

### InnerBlocks

```javascript
import { InnerBlocks, useInnerBlocksProps } from '@wordpress/block-editor';

// Basic usage
<InnerBlocks
    allowedBlocks={ [ 'core/paragraph', 'core/heading' ] }
    template={ [
        [ 'core/heading', { level: 2 } ],
        [ 'core/paragraph', {} ],
    ] }
    templateLock="all" // 'all' | 'insert' | 'contentOnly' | false
    orientation="vertical" // 'vertical' | 'horizontal'
    renderAppender={ InnerBlocks.DefaultBlockAppender }
/>

// With useInnerBlocksProps
const { children, ...innerBlocksProps } = useInnerBlocksProps(
    useBlockProps(),
    {
        allowedBlocks: [ 'core/paragraph' ],
        template: [ [ 'core/paragraph', {} ] ],
    }
);
return <div { ...innerBlocksProps }>{ children }</div>;

// Save
<InnerBlocks.Content />
```

### URLInput

```javascript
import { URLInput, URLInputButton } from '@wordpress/block-editor';

// Full input
<URLInput
    value={ url }
    onChange={ ( value ) => setAttributes( { url: value } ) }
    placeholder="Enter URL..."
/>

// Button with popover
<URLInputButton
    url={ url }
    onChange={ ( value ) => setAttributes( { url: value } ) }
/>
```

## WordPress Components

Import from `@wordpress/components`:

### PanelBody & PanelRow

```javascript
import { PanelBody, PanelRow } from '@wordpress/components';

<PanelBody title="Panel Title" initialOpen={ false }>
    <PanelRow>
        <p>Panel content</p>
    </PanelRow>
</PanelBody>
```

### TextControl

```javascript
import { TextControl } from '@wordpress/components';

<TextControl
    label="Title"
    value={ title }
    onChange={ ( value ) => setAttributes( { title: value } ) }
    placeholder="Enter title..."
    help="Help text below the input"
/>
```

### TextareaControl

```javascript
import { TextareaControl } from '@wordpress/components';

<TextareaControl
    label="Description"
    value={ description }
    onChange={ ( value ) => setAttributes( { description: value } ) }
    rows={ 4 }
/>
```

### ToggleControl

```javascript
import { ToggleControl } from '@wordpress/components';

<ToggleControl
    label="Show Title"
    checked={ showTitle }
    onChange={ ( value ) => setAttributes( { showTitle: value } ) }
    help={ showTitle ? 'Title is visible' : 'Title is hidden' }
/>
```

### SelectControl

```javascript
import { SelectControl } from '@wordpress/components';

<SelectControl
    label="Layout"
    value={ layout }
    options={ [
        { label: 'Grid', value: 'grid' },
        { label: 'List', value: 'list' },
        { label: 'Carousel', value: 'carousel' },
    ] }
    onChange={ ( value ) => setAttributes( { layout: value } ) }
    help="Choose display layout"
/>

// Multiple selection
<SelectControl
    multiple
    label="Categories"
    value={ selectedCategories }
    options={ categories }
    onChange={ ( value ) => setAttributes( { selectedCategories: value } ) }
/>
```

### RangeControl

```javascript
import { RangeControl } from '@wordpress/components';

<RangeControl
    label="Columns"
    value={ columns }
    onChange={ ( value ) => setAttributes( { columns: value } ) }
    min={ 1 }
    max={ 6 }
    step={ 1 }
    marks={ [
        { value: 1, label: '1' },
        { value: 3, label: '3' },
        { value: 6, label: '6' },
    ] }
    withInputField={ true }
    resetFallbackValue={ 3 }
/>
```

### RadioControl

```javascript
import { RadioControl } from '@wordpress/components';

<RadioControl
    label="Size"
    selected={ size }
    options={ [
        { label: 'Small', value: 'small' },
        { label: 'Medium', value: 'medium' },
        { label: 'Large', value: 'large' },
    ] }
    onChange={ ( value ) => setAttributes( { size: value } ) }
/>
```

### CheckboxControl

```javascript
import { CheckboxControl } from '@wordpress/components';

<CheckboxControl
    label="Enable feature"
    checked={ isEnabled }
    onChange={ ( value ) => setAttributes( { isEnabled: value } ) }
    help="Enable this feature"
/>
```

### ColorPicker & ColorPalette

```javascript
import { ColorPicker, ColorPalette } from '@wordpress/components';

// Full picker
<ColorPicker
    color={ color }
    onChange={ ( value ) => setAttributes( { color: value } ) }
    enableAlpha
    defaultValue="#000"
/>

// Palette
<ColorPalette
    colors={ [
        { name: 'Red', color: '#f00' },
        { name: 'Blue', color: '#00f' },
    ] }
    value={ color }
    onChange={ ( value ) => setAttributes( { color: value } ) }
    clearable={ true }
/>
```

### Button

```javascript
import { Button } from '@wordpress/components';

<Button
    variant="primary" // 'primary' | 'secondary' | 'tertiary' | 'link'
    size="default" // 'default' | 'compact' | 'small'
    icon="edit"
    iconPosition="left"
    disabled={ isDisabled }
    isBusy={ isLoading }
    isDestructive={ false }
    onClick={ handleClick }
>
    Button Text
</Button>
```

### Icon

```javascript
import { Icon } from '@wordpress/components';
import { edit, trash } from '@wordpress/icons';

<Icon icon={ edit } size={ 24 } />
<Icon icon="admin-post" /> {/* Dashicon */}
```

### Modal

```javascript
import { Modal, Button } from '@wordpress/components';
import { useState } from '@wordpress/element';

const [ isOpen, setOpen ] = useState( false );

{ isOpen && (
    <Modal
        title="Modal Title"
        onRequestClose={ () => setOpen( false ) }
        isDismissible={ true }
        shouldCloseOnEsc={ true }
        shouldCloseOnClickOutside={ true }
    >
        <p>Modal content</p>
        <Button variant="primary" onClick={ () => setOpen( false ) }>
            Close
        </Button>
    </Modal>
) }
```

### Notice

```javascript
import { Notice } from '@wordpress/components';

<Notice
    status="success" // 'success' | 'info' | 'warning' | 'error'
    isDismissible={ true }
    onRemove={ () => setShowNotice( false ) }
    actions={ [
        { label: 'Undo', onClick: handleUndo },
    ] }
>
    Notice message
</Notice>
```

### Spinner

```javascript
import { Spinner } from '@wordpress/components';

{ isLoading && <Spinner /> }
```

### Placeholder

```javascript
import { Placeholder } from '@wordpress/components';

<Placeholder
    icon="admin-post"
    label="Block Title"
    instructions="Configure block settings"
>
    <Button variant="primary">Configure</Button>
</Placeholder>
```

### Popover

```javascript
import { Popover, Button } from '@wordpress/components';
import { useState } from '@wordpress/element';

const [ isVisible, setIsVisible ] = useState( false );

<Button onClick={ () => setIsVisible( ! isVisible ) }>
    Toggle Popover
    { isVisible && (
        <Popover
            position="bottom center"
            onClose={ () => setIsVisible( false ) }
        >
            Popover content
        </Popover>
    ) }
</Button>
```

### TabPanel

```javascript
import { TabPanel } from '@wordpress/components';

<TabPanel
    tabs={ [
        { name: 'tab1', title: 'Tab 1' },
        { name: 'tab2', title: 'Tab 2' },
    ] }
    initialTabName="tab1"
>
    { ( tab ) => (
        <div>Content for { tab.name }</div>
    ) }
</TabPanel>
```

### DateTimePicker

```javascript
import { DateTimePicker } from '@wordpress/components';

<DateTimePicker
    currentDate={ date }
    onChange={ ( value ) => setAttributes( { date: value } ) }
    is12Hour={ true }
/>
```

### FormTokenField

```javascript
import { FormTokenField } from '@wordpress/components';

<FormTokenField
    label="Tags"
    value={ selectedTags }
    suggestions={ availableTags }
    onChange={ ( value ) => setAttributes( { selectedTags: value } ) }
    maxSuggestions={ 10 }
/>
```

### FontSizePicker

```javascript
import { FontSizePicker } from '@wordpress/components';

<FontSizePicker
    fontSizes={ [
        { name: 'Small', slug: 'small', size: 12 },
        { name: 'Normal', slug: 'normal', size: 16 },
        { name: 'Large', slug: 'large', size: 24 },
    ] }
    value={ fontSize }
    onChange={ ( value ) => setAttributes( { fontSize: value } ) }
    fallbackFontSize={ 16 }
    withSlider
/>
```
