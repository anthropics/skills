---
name: gutenberg
description: WordPress Block Editor (Gutenberg) development expert for creating custom blocks, block patterns, block variations, and extending the editor. Use when building React-based WordPress blocks, working with block.json configuration, InnerBlocks, RichText components, block controls, Server-Side Rendering, or any Gutenberg/Block Editor development task.
---

# Gutenberg Block Development Guide

Expert guidance for WordPress Block Editor development using React and modern JavaScript.

## Block Structure

```
my-block/
├── block.json          # Block metadata (required)
├── index.js            # Block registration
├── edit.js             # Editor component
├── save.js             # Frontend save component
├── editor.scss         # Editor-only styles
├── style.scss          # Frontend + editor styles
├── render.php          # Server-side render (dynamic blocks)
└── view.js             # Frontend JavaScript
```

## block.json Configuration

```json
{
    "$schema": "https://schemas.wp.org/trunk/block.json",
    "apiVersion": 3,
    "name": "my-plugin/my-block",
    "version": "1.0.0",
    "title": "My Block",
    "category": "widgets",
    "icon": "smiley",
    "description": "A custom block description.",
    "keywords": ["custom", "block"],
    "textdomain": "my-plugin",
    "attributes": {
        "content": {
            "type": "string",
            "source": "html",
            "selector": "p"
        },
        "alignment": {
            "type": "string",
            "default": "none"
        },
        "backgroundColor": {
            "type": "string"
        },
        "showTitle": {
            "type": "boolean",
            "default": true
        },
        "columns": {
            "type": "number",
            "default": 3
        },
        "items": {
            "type": "array",
            "default": []
        },
        "mediaId": {
            "type": "number"
        },
        "mediaUrl": {
            "type": "string",
            "source": "attribute",
            "selector": "img",
            "attribute": "src"
        }
    },
    "supports": {
        "html": false,
        "align": ["wide", "full"],
        "anchor": true,
        "className": true,
        "color": {
            "background": true,
            "text": true,
            "gradients": true,
            "link": true
        },
        "spacing": {
            "margin": true,
            "padding": true,
            "blockGap": true
        },
        "typography": {
            "fontSize": true,
            "lineHeight": true
        },
        "__experimentalBorder": {
            "radius": true,
            "width": true,
            "color": true,
            "style": true
        }
    },
    "example": {
        "attributes": {
            "content": "Example content"
        }
    },
    "editorScript": "file:./index.js",
    "editorStyle": "file:./editor.css",
    "style": "file:./style.css",
    "viewScript": "file:./view.js",
    "render": "file:./render.php"
}
```

## Block Registration

### index.js

```javascript
import { registerBlockType } from '@wordpress/blocks';
import { __ } from '@wordpress/i18n';

import Edit from './edit';
import Save from './save';
import metadata from './block.json';

import './style.scss';
import './editor.scss';

registerBlockType( metadata.name, {
    edit: Edit,
    save: Save,
} );
```

## Edit Component

### Basic Edit Component

```javascript
import { __ } from '@wordpress/i18n';
import {
    useBlockProps,
    RichText,
    InspectorControls,
    BlockControls,
    AlignmentToolbar,
    MediaUpload,
    MediaUploadCheck,
    InnerBlocks,
    PanelColorSettings,
} from '@wordpress/block-editor';
import {
    PanelBody,
    PanelRow,
    TextControl,
    ToggleControl,
    SelectControl,
    RangeControl,
    Button,
    Placeholder,
} from '@wordpress/components';

export default function Edit( { attributes, setAttributes } ) {
    const {
        content,
        alignment,
        backgroundColor,
        showTitle,
        columns,
        mediaId,
        mediaUrl,
    } = attributes;

    const blockProps = useBlockProps( {
        className: `align-${ alignment }`,
        style: { backgroundColor },
    } );

    const onSelectMedia = ( media ) => {
        setAttributes( {
            mediaId: media.id,
            mediaUrl: media.url,
        } );
    };

    const onRemoveMedia = () => {
        setAttributes( {
            mediaId: undefined,
            mediaUrl: undefined,
        } );
    };

    return (
        <>
            <InspectorControls>
                <PanelBody title={ __( 'Settings', 'my-plugin' ) }>
                    <ToggleControl
                        label={ __( 'Show Title', 'my-plugin' ) }
                        checked={ showTitle }
                        onChange={ ( value ) =>
                            setAttributes( { showTitle: value } )
                        }
                    />
                    <RangeControl
                        label={ __( 'Columns', 'my-plugin' ) }
                        value={ columns }
                        onChange={ ( value ) =>
                            setAttributes( { columns: value } )
                        }
                        min={ 1 }
                        max={ 6 }
                    />
                    <SelectControl
                        label={ __( 'Layout', 'my-plugin' ) }
                        value={ alignment }
                        options={ [
                            { label: __( 'None', 'my-plugin' ), value: 'none' },
                            { label: __( 'Left', 'my-plugin' ), value: 'left' },
                            { label: __( 'Center', 'my-plugin' ), value: 'center' },
                            { label: __( 'Right', 'my-plugin' ), value: 'right' },
                        ] }
                        onChange={ ( value ) =>
                            setAttributes( { alignment: value } )
                        }
                    />
                </PanelBody>
                <PanelColorSettings
                    title={ __( 'Color Settings', 'my-plugin' ) }
                    colorSettings={ [
                        {
                            value: backgroundColor,
                            onChange: ( value ) =>
                                setAttributes( { backgroundColor: value } ),
                            label: __( 'Background Color', 'my-plugin' ),
                        },
                    ] }
                />
            </InspectorControls>

            <BlockControls>
                <AlignmentToolbar
                    value={ alignment }
                    onChange={ ( value ) =>
                        setAttributes( { alignment: value } )
                    }
                />
            </BlockControls>

            <div { ...blockProps }>
                <MediaUploadCheck>
                    { ! mediaUrl ? (
                        <MediaUpload
                            onSelect={ onSelectMedia }
                            allowedTypes={ [ 'image' ] }
                            value={ mediaId }
                            render={ ( { open } ) => (
                                <Placeholder
                                    icon="format-image"
                                    label={ __( 'Image', 'my-plugin' ) }
                                >
                                    <Button variant="primary" onClick={ open }>
                                        { __( 'Select Image', 'my-plugin' ) }
                                    </Button>
                                </Placeholder>
                            ) }
                        />
                    ) : (
                        <div className="image-wrapper">
                            <img src={ mediaUrl } alt="" />
                            <Button
                                onClick={ onRemoveMedia }
                                isDestructive
                            >
                                { __( 'Remove', 'my-plugin' ) }
                            </Button>
                        </div>
                    ) }
                </MediaUploadCheck>

                <RichText
                    tagName="p"
                    value={ content }
                    onChange={ ( value ) =>
                        setAttributes( { content: value } )
                    }
                    placeholder={ __( 'Enter content...', 'my-plugin' ) }
                />
            </div>
        </>
    );
}
```

## Save Component

### Static Save

```javascript
import { useBlockProps, RichText } from '@wordpress/block-editor';

export default function Save( { attributes } ) {
    const { content, alignment, backgroundColor, mediaUrl } = attributes;

    const blockProps = useBlockProps.save( {
        className: `align-${ alignment }`,
        style: { backgroundColor },
    } );

    return (
        <div { ...blockProps }>
            { mediaUrl && <img src={ mediaUrl } alt="" /> }
            <RichText.Content tagName="p" value={ content } />
        </div>
    );
}
```

### Dynamic Block (Server-Side Render)

```javascript
// save.js - Return null for dynamic blocks
export default function Save() {
    return null;
}
```

```php
<?php
// render.php - Server-side rendering
/**
 * @var array    $attributes Block attributes.
 * @var string   $content    Block default content.
 * @var WP_Block $block      Block instance.
 */

$wrapper_attributes = get_block_wrapper_attributes( array(
    'class' => 'align-' . esc_attr( $attributes['alignment'] ?? 'none' ),
    'style' => isset( $attributes['backgroundColor'] )
        ? 'background-color: ' . esc_attr( $attributes['backgroundColor'] )
        : '',
) );
?>
<div <?php echo $wrapper_attributes; ?>>
    <?php if ( ! empty( $attributes['mediaUrl'] ) ) : ?>
        <img src="<?php echo esc_url( $attributes['mediaUrl'] ); ?>" alt="">
    <?php endif; ?>
    <?php if ( ! empty( $attributes['content'] ) ) : ?>
        <p><?php echo wp_kses_post( $attributes['content'] ); ?></p>
    <?php endif; ?>
</div>
```

## InnerBlocks

```javascript
import { useBlockProps, InnerBlocks } from '@wordpress/block-editor';

const ALLOWED_BLOCKS = [ 'core/paragraph', 'core/image', 'core/heading' ];

const TEMPLATE = [
    [ 'core/heading', { placeholder: 'Title' } ],
    [ 'core/paragraph', { placeholder: 'Description' } ],
];

export default function Edit() {
    const blockProps = useBlockProps();

    return (
        <div { ...blockProps }>
            <InnerBlocks
                allowedBlocks={ ALLOWED_BLOCKS }
                template={ TEMPLATE }
                templateLock="all" // 'all', 'insert', false
                orientation="horizontal" // 'horizontal', 'vertical'
            />
        </div>
    );
}

export function Save() {
    const blockProps = useBlockProps.save();

    return (
        <div { ...blockProps }>
            <InnerBlocks.Content />
        </div>
    );
}
```

## Block Patterns

### PHP Registration

```php
add_action( 'init', 'my_plugin_register_patterns' );
function my_plugin_register_patterns() {
    register_block_pattern(
        'my-plugin/hero-section',
        array(
            'title'       => __( 'Hero Section', 'my-plugin' ),
            'description' => __( 'A hero section with image and text.', 'my-plugin' ),
            'categories'  => array( 'featured', 'banner' ),
            'keywords'    => array( 'hero', 'banner', 'header' ),
            'content'     => '<!-- wp:group {"align":"full","style":{"spacing":{"padding":{"top":"100px","bottom":"100px"}}}} -->
                <div class="wp-block-group alignfull" style="padding-top:100px;padding-bottom:100px">
                    <!-- wp:heading {"textAlign":"center","level":1} -->
                    <h1 class="has-text-align-center">Hero Title</h1>
                    <!-- /wp:heading -->
                    <!-- wp:paragraph {"align":"center"} -->
                    <p class="has-text-align-center">Hero description text goes here.</p>
                    <!-- /wp:paragraph -->
                    <!-- wp:buttons {"layout":{"type":"flex","justifyContent":"center"}} -->
                    <div class="wp-block-buttons">
                        <!-- wp:button -->
                        <div class="wp-block-button"><a class="wp-block-button__link wp-element-button">Get Started</a></div>
                        <!-- /wp:button -->
                    </div>
                    <!-- /wp:buttons -->
                </div>
                <!-- /wp:group -->',
        )
    );

    // Register pattern category
    register_block_pattern_category(
        'my-plugin',
        array( 'label' => __( 'My Plugin Patterns', 'my-plugin' ) )
    );
}
```

### Pattern File (patterns/hero.php)

```php
<?php
/**
 * Title: Hero Section
 * Slug: my-plugin/hero
 * Categories: featured, banner
 * Keywords: hero, header, banner
 * Block Types: core/post-content
 * Viewport Width: 1400
 */
?>
<!-- wp:cover {"dimRatio":50,"minHeight":500} -->
<div class="wp-block-cover" style="min-height:500px">
    <span class="wp-block-cover__background has-background-dim"></span>
    <div class="wp-block-cover__inner-container">
        <!-- wp:heading {"textAlign":"center","level":1} -->
        <h1 class="has-text-align-center"><?php esc_html_e( 'Welcome', 'my-plugin' ); ?></h1>
        <!-- /wp:heading -->
    </div>
</div>
<!-- /wp:cover -->
```

## Block Variations

```javascript
import { registerBlockVariation } from '@wordpress/blocks';

registerBlockVariation( 'core/group', {
    name: 'my-card',
    title: 'Card',
    description: 'A card container with shadow',
    icon: 'id',
    scope: [ 'inserter', 'transform' ],
    attributes: {
        className: 'is-style-card',
        style: {
            spacing: { padding: { top: '20px', bottom: '20px', left: '20px', right: '20px' } },
            border: { radius: '8px' },
        },
    },
    innerBlocks: [
        [ 'core/heading', { level: 3, placeholder: 'Card Title' } ],
        [ 'core/paragraph', { placeholder: 'Card content...' } ],
    ],
    isActive: ( blockAttributes ) =>
        blockAttributes.className?.includes( 'is-style-card' ),
} );
```

## Block Styles

```javascript
import { registerBlockStyle, unregisterBlockStyle } from '@wordpress/blocks';

// Register style
registerBlockStyle( 'core/button', {
    name: 'outline',
    label: 'Outline',
} );

registerBlockStyle( 'core/image', {
    name: 'rounded',
    label: 'Rounded',
    isDefault: true,
} );

// Unregister style
wp.domReady( () => {
    unregisterBlockStyle( 'core/button', 'fill' );
} );
```

```css
/* style.scss */
.wp-block-button.is-style-outline .wp-block-button__link {
    background: transparent;
    border: 2px solid currentColor;
}

.wp-block-image.is-style-rounded img {
    border-radius: 50%;
}
```

## Hooks & Filters

### Block Registration Filters

```javascript
import { addFilter } from '@wordpress/hooks';

// Modify block settings
addFilter(
    'blocks.registerBlockType',
    'my-plugin/modify-block',
    ( settings, name ) => {
        if ( name === 'core/paragraph' ) {
            return {
                ...settings,
                supports: {
                    ...settings.supports,
                    color: {
                        background: true,
                        text: true,
                    },
                },
            };
        }
        return settings;
    }
);

// Add custom attributes
addFilter(
    'blocks.registerBlockType',
    'my-plugin/add-attributes',
    ( settings, name ) => {
        if ( name === 'core/image' ) {
            settings.attributes = {
                ...settings.attributes,
                customCaption: {
                    type: 'string',
                    default: '',
                },
            };
        }
        return settings;
    }
);
```

### Editor Filters

```javascript
import { createHigherOrderComponent } from '@wordpress/compose';

// Wrap BlockEdit component
const withCustomControls = createHigherOrderComponent( ( BlockEdit ) => {
    return ( props ) => {
        if ( props.name !== 'core/paragraph' ) {
            return <BlockEdit { ...props } />;
        }

        return (
            <>
                <BlockEdit { ...props } />
                <InspectorControls>
                    <PanelBody title="Custom Settings">
                        {/* Custom controls */}
                    </PanelBody>
                </InspectorControls>
            </>
        );
    };
}, 'withCustomControls' );

addFilter(
    'editor.BlockEdit',
    'my-plugin/custom-controls',
    withCustomControls
);
```

### PHP Filters

```php
// Modify block output
add_filter( 'render_block', 'my_plugin_modify_block_output', 10, 2 );
function my_plugin_modify_block_output( $block_content, $block ) {
    if ( 'core/paragraph' !== $block['blockName'] ) {
        return $block_content;
    }

    // Wrap paragraph in custom div
    return '<div class="my-paragraph-wrapper">' . $block_content . '</div>';
}

// Filter specific block
add_filter( 'render_block_core/image', 'my_plugin_modify_image_block', 10, 2 );
function my_plugin_modify_image_block( $block_content, $block ) {
    // Add lazy loading
    return str_replace( '<img', '<img loading="lazy"', $block_content );
}
```

## Build Setup

### package.json

```json
{
    "name": "my-plugin-blocks",
    "version": "1.0.0",
    "scripts": {
        "build": "wp-scripts build",
        "start": "wp-scripts start",
        "lint:js": "wp-scripts lint-js",
        "lint:css": "wp-scripts lint-style",
        "format": "wp-scripts format"
    },
    "devDependencies": {
        "@wordpress/scripts": "^27.0.0"
    }
}
```

### webpack.config.js (optional customization)

```javascript
const defaultConfig = require( '@wordpress/scripts/config/webpack.config' );

module.exports = {
    ...defaultConfig,
    entry: {
        'block-one': './src/block-one',
        'block-two': './src/block-two',
    },
};
```

## References

For detailed information:
- **Components reference**: See [references/components.md](references/components.md)
- **Data & state management**: See [references/data-store.md](references/data-store.md)
