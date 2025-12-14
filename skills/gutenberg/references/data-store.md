# Gutenberg Data & State Management

## WordPress Data Stores

### Core Stores

| Store | Purpose |
|-------|---------|
| `core` | Entity data (posts, users, taxonomies) |
| `core/block-editor` | Block editor state |
| `core/editor` | Post editor state |
| `core/notices` | Admin notices |
| `core/preferences` | User preferences |

### Accessing Data

```javascript
import { useSelect, useDispatch } from '@wordpress/data';
import { store as coreStore } from '@wordpress/core-data';
import { store as blockEditorStore } from '@wordpress/block-editor';
import { store as editorStore } from '@wordpress/editor';
```

## useSelect Hook

```javascript
import { useSelect } from '@wordpress/data';
import { store as coreStore } from '@wordpress/core-data';

function MyComponent() {
    // Get posts
    const posts = useSelect( ( select ) => {
        return select( coreStore ).getEntityRecords( 'postType', 'post', {
            per_page: 10,
            status: 'publish',
        } );
    }, [] );

    // Get current post
    const { currentPost, isAutosaving, isSaving } = useSelect( ( select ) => {
        const editor = select( 'core/editor' );
        return {
            currentPost: editor.getCurrentPost(),
            isAutosaving: editor.isAutosavingPost(),
            isSaving: editor.isSavingPost(),
        };
    }, [] );

    // Get selected block
    const { selectedBlock, selectedBlockClientId } = useSelect( ( select ) => {
        const blockEditor = select( 'core/block-editor' );
        return {
            selectedBlock: blockEditor.getSelectedBlock(),
            selectedBlockClientId: blockEditor.getSelectedBlockClientId(),
        };
    }, [] );

    // Multiple selectors
    const { posts, categories, authors } = useSelect( ( select ) => {
        const { getEntityRecords } = select( coreStore );
        return {
            posts: getEntityRecords( 'postType', 'post', { per_page: 5 } ),
            categories: getEntityRecords( 'taxonomy', 'category' ),
            authors: getEntityRecords( 'root', 'user' ),
        };
    }, [] );
}
```

## useDispatch Hook

```javascript
import { useDispatch } from '@wordpress/data';
import { store as coreStore } from '@wordpress/core-data';
import { store as noticesStore } from '@wordpress/notices';

function MyComponent() {
    const { saveEntityRecord, deleteEntityRecord } = useDispatch( coreStore );
    const { createSuccessNotice, createErrorNotice } = useDispatch( noticesStore );

    const handleSave = async () => {
        try {
            await saveEntityRecord( 'postType', 'post', {
                id: postId,
                title: newTitle,
            } );
            createSuccessNotice( 'Post saved successfully!', {
                type: 'snackbar',
            } );
        } catch ( error ) {
            createErrorNotice( 'Error saving post', {
                type: 'snackbar',
            } );
        }
    };

    const handleDelete = async () => {
        await deleteEntityRecord( 'postType', 'post', postId );
    };
}
```

## Core Data Selectors

### Entity Records

```javascript
const { getEntityRecords, getEntityRecord, hasFinishedResolution } = select( coreStore );

// Get multiple records
const posts = getEntityRecords( 'postType', 'post', {
    per_page: 10,
    page: 1,
    status: 'publish',
    categories: [ 1, 2 ],
    search: 'query',
    orderby: 'date',
    order: 'desc',
    _embed: true, // Include embedded data
} );

// Get single record
const post = getEntityRecord( 'postType', 'post', postId );

// Check if loading
const isLoading = ! hasFinishedResolution( 'getEntityRecords', [
    'postType',
    'post',
    { per_page: 10 },
] );

// Get taxonomies
const categories = getEntityRecords( 'taxonomy', 'category' );
const tags = getEntityRecords( 'taxonomy', 'post_tag' );

// Get users
const users = getEntityRecords( 'root', 'user', { per_page: -1 } );

// Get site settings
const siteSettings = getEntityRecord( 'root', 'site' );

// Get media
const media = getEntityRecords( 'postType', 'attachment', {
    per_page: 20,
    media_type: 'image',
} );
```

### Block Editor Selectors

```javascript
const blockEditor = select( 'core/block-editor' );

// Selected block
blockEditor.getSelectedBlock();
blockEditor.getSelectedBlockClientId();
blockEditor.getSelectedBlockClientIds(); // Multi-selection
blockEditor.hasSelectedBlock();

// Block data
blockEditor.getBlock( clientId );
blockEditor.getBlocks(); // All root blocks
blockEditor.getBlockCount();
blockEditor.getBlockName( clientId );
blockEditor.getBlockAttributes( clientId );
blockEditor.getBlockIndex( clientId );
blockEditor.getBlockParents( clientId );
blockEditor.getBlockRootClientId( clientId );

// Inner blocks
blockEditor.getBlockOrder( clientId ); // Child client IDs
blockEditor.getClientIdsOfDescendants( [ clientId ] );

// Block insertion
blockEditor.getInserterItems();
blockEditor.canInsertBlockType( 'core/paragraph', rootClientId );

// Selection
blockEditor.getSelectionStart();
blockEditor.getSelectionEnd();
blockEditor.isBlockSelected( clientId );
blockEditor.hasMultiSelection();
```

### Editor Selectors

```javascript
const editor = select( 'core/editor' );

// Current post
editor.getCurrentPost();
editor.getCurrentPostId();
editor.getCurrentPostType();
editor.getCurrentPostAttribute( 'title' );
editor.getEditedPostAttribute( 'title' ); // Edited value
editor.getEditedPostContent();

// Post status
editor.isEditedPostDirty();
editor.isEditedPostSaveable();
editor.isEditedPostPublishable();
editor.isCurrentPostPublished();
editor.isCurrentPostScheduled();

// Saving status
editor.isSavingPost();
editor.isAutosavingPost();
editor.isPublishingPost();

// Meta
editor.getEditedPostAttribute( 'meta' );
```

## Core Data Actions

```javascript
const { saveEntityRecord, editEntityRecord, deleteEntityRecord } = dispatch( coreStore );

// Save new record
const newPost = await saveEntityRecord( 'postType', 'post', {
    title: 'New Post',
    content: 'Content here',
    status: 'draft',
} );

// Edit existing (stage changes without saving)
editEntityRecord( 'postType', 'post', postId, {
    title: 'Updated Title',
} );

// Save existing
await saveEntityRecord( 'postType', 'post', {
    id: postId,
    title: 'Updated Title',
} );

// Delete
await deleteEntityRecord( 'postType', 'post', postId, {
    force: true, // Skip trash
} );
```

## Block Editor Actions

```javascript
const {
    insertBlock,
    insertBlocks,
    removeBlock,
    removeBlocks,
    replaceBlock,
    updateBlockAttributes,
    selectBlock,
    moveBlocksUp,
    moveBlocksDown,
} = dispatch( 'core/block-editor' );

import { createBlock } from '@wordpress/blocks';

// Insert single block
const newBlock = createBlock( 'core/paragraph', {
    content: 'New paragraph',
} );
insertBlock( newBlock, index, rootClientId );

// Insert multiple blocks
insertBlocks( [ block1, block2 ], index, rootClientId );

// Remove block
removeBlock( clientId );
removeBlocks( [ clientId1, clientId2 ] );

// Replace block
replaceBlock( clientId, newBlock );

// Update attributes
updateBlockAttributes( clientId, { content: 'Updated' } );

// Select block
selectBlock( clientId );

// Move blocks
moveBlocksUp( [ clientId ] );
moveBlocksDown( [ clientId ] );
```

## Notices Actions

```javascript
const { createNotice, createSuccessNotice, createErrorNotice, removeNotice } =
    dispatch( 'core/notices' );

// Generic notice
createNotice( 'info', 'Message here', {
    id: 'my-notice-id',
    isDismissible: true,
    type: 'snackbar', // 'default' | 'snackbar'
    speak: true,
    actions: [
        {
            label: 'Undo',
            onClick: () => handleUndo(),
        },
    ],
} );

// Shorthand methods
createSuccessNotice( 'Saved!', { type: 'snackbar' } );
createErrorNotice( 'Error occurred', { type: 'snackbar' } );

// Remove notice
removeNotice( 'my-notice-id' );
```

## Custom Data Store

```javascript
import { createReduxStore, register } from '@wordpress/data';

const DEFAULT_STATE = {
    items: [],
    isLoading: false,
};

const actions = {
    setItems( items ) {
        return { type: 'SET_ITEMS', items };
    },
    addItem( item ) {
        return { type: 'ADD_ITEM', item };
    },
    fetchItems() {
        return async ( { dispatch } ) => {
            const response = await apiFetch( { path: '/my-plugin/v1/items' } );
            dispatch.setItems( response );
        };
    },
};

const selectors = {
    getItems( state ) {
        return state.items;
    },
    getItemById( state, id ) {
        return state.items.find( ( item ) => item.id === id );
    },
};

const reducer = ( state = DEFAULT_STATE, action ) => {
    switch ( action.type ) {
        case 'SET_ITEMS':
            return { ...state, items: action.items };
        case 'ADD_ITEM':
            return { ...state, items: [ ...state.items, action.item ] };
        default:
            return state;
    }
};

const store = createReduxStore( 'my-plugin/store', {
    reducer,
    actions,
    selectors,
} );

register( store );

// Usage
const items = useSelect( ( select ) => select( 'my-plugin/store' ).getItems() );
const { fetchItems, addItem } = useDispatch( 'my-plugin/store' );
```

## useEntityProp Hook

```javascript
import { useEntityProp } from '@wordpress/core-data';

function PostTitleEditor() {
    const [ title, setTitle ] = useEntityProp(
        'postType',
        'post',
        'title',
        postId // Optional, defaults to current post
    );

    return (
        <TextControl
            label="Title"
            value={ title }
            onChange={ setTitle }
        />
    );
}

// Meta fields
function PostMetaEditor() {
    const [ meta, setMeta ] = useEntityProp( 'postType', 'post', 'meta' );

    const updateMeta = ( key, value ) => {
        setMeta( { ...meta, [ key ]: value } );
    };

    return (
        <TextControl
            label="Custom Field"
            value={ meta?.my_custom_field || '' }
            onChange={ ( value ) => updateMeta( 'my_custom_field', value ) }
        />
    );
}
```

## API Fetch

```javascript
import apiFetch from '@wordpress/api-fetch';

// GET request
const posts = await apiFetch( { path: '/wp/v2/posts' } );

// POST request
const newPost = await apiFetch( {
    path: '/wp/v2/posts',
    method: 'POST',
    data: {
        title: 'New Post',
        content: 'Content',
        status: 'draft',
    },
} );

// With query params
const posts = await apiFetch( {
    path: addQueryArgs( '/wp/v2/posts', {
        per_page: 10,
        status: 'publish',
    } ),
} );

// Custom endpoint
const result = await apiFetch( {
    path: '/my-plugin/v1/custom-endpoint',
    method: 'POST',
    data: { key: 'value' },
} );
```
