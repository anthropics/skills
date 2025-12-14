# GenerateBlocks Block Attributes Reference

## Container Block Attributes

### Layout

| Attribute | Type | Description |
|-----------|------|-------------|
| `tagName` | string | HTML tag (div, section, article, aside, header, footer, main, nav) |
| `display` | string | CSS display (block, flex, inline, inline-block, none) |
| `isGrid` | boolean | Enable Flexbox layout |
| `flexDirection` | string | flex-direction value |
| `flexWrap` | string | flex-wrap value |
| `alignItems` | string | align-items value |
| `justifyContent` | string | justify-content value |
| `columnGap` | string | Column gap with unit |
| `rowGap` | string | Row gap with unit |

### Sizing

| Attribute | Type | Description |
|-----------|------|-------------|
| `width` | number | Desktop width (%) |
| `widthTablet` | number | Tablet width (%) |
| `widthMobile` | number | Mobile width (%) |
| `minHeight` | string | Minimum height with unit |
| `minHeightTablet` | string | Tablet min height |
| `minHeightMobile` | string | Mobile min height |
| `verticalAlignment` | string | Vertical align for min-height |

### Spacing

| Attribute | Type | Description |
|-----------|------|-------------|
| `paddingTop` | string | Top padding with unit |
| `paddingRight` | string | Right padding with unit |
| `paddingBottom` | string | Bottom padding with unit |
| `paddingLeft` | string | Left padding with unit |
| `paddingTopTablet` | string | Tablet top padding |
| `paddingRightTablet` | string | Tablet right padding |
| `paddingBottomTablet` | string | Tablet bottom padding |
| `paddingLeftTablet` | string | Tablet left padding |
| `paddingTopMobile` | string | Mobile top padding |
| `paddingRightMobile` | string | Mobile right padding |
| `paddingBottomMobile` | string | Mobile bottom padding |
| `paddingLeftMobile` | string | Mobile left padding |
| `marginTop` | string | Top margin |
| `marginRight` | string | Right margin |
| `marginBottom` | string | Bottom margin |
| `marginLeft` | string | Left margin |
| `marginTopTablet` | string | Tablet top margin |
| `marginRightTablet` | string | Tablet right margin |
| `marginBottomTablet` | string | Tablet bottom margin |
| `marginLeftTablet` | string | Tablet left margin |
| `marginTopMobile` | string | Mobile top margin |
| `marginRightMobile` | string | Mobile right margin |
| `marginBottomMobile` | string | Mobile bottom margin |
| `marginLeftMobile` | string | Mobile left margin |

### Background

| Attribute | Type | Description |
|-----------|------|-------------|
| `backgroundColor` | string | Background color |
| `backgroundColorOpacity` | number | Background opacity (0-1) |
| `gradient` | string | CSS gradient |
| `bgImage` | object | Background image settings |
| `bgImage.id` | number | Image ID |
| `bgImage.url` | string | Image URL |
| `bgImageSize` | string | Background size |
| `bgImagePosition` | string | Background position |
| `bgImageRepeat` | string | Background repeat |
| `bgImageAttachment` | string | Background attachment |

### Border

| Attribute | Type | Description |
|-----------|------|-------------|
| `borderSizeTop` | string | Top border width |
| `borderSizeRight` | string | Right border width |
| `borderSizeBottom` | string | Bottom border width |
| `borderSizeLeft` | string | Left border width |
| `borderColor` | string | Border color |
| `borderRadius` | string | Border radius (all) |
| `borderRadiusTopLeft` | string | Top-left radius |
| `borderRadiusTopRight` | string | Top-right radius |
| `borderRadiusBottomRight` | string | Bottom-right radius |
| `borderRadiusBottomLeft` | string | Bottom-left radius |

### Advanced

| Attribute | Type | Description |
|-----------|------|-------------|
| `uniqueId` | string | Unique block identifier |
| `anchor` | string | HTML anchor |
| `className` | string | Additional CSS classes |
| `zIndex` | number | Z-index value |
| `overflow` | string | CSS overflow |
| `position` | string | CSS position |

## Button Block Attributes

### Content

| Attribute | Type | Description |
|-----------|------|-------------|
| `text` | string | Button text |
| `url` | string | Link URL |
| `target` | string | Link target (_self, _blank) |
| `rel` | string | Link rel attribute |

### Styling

| Attribute | Type | Description |
|-----------|------|-------------|
| `backgroundColor` | string | Background color |
| `backgroundColorHover` | string | Hover background color |
| `textColor` | string | Text color |
| `textColorHover` | string | Hover text color |
| `fontSize` | string | Font size |
| `fontSizeTablet` | string | Tablet font size |
| `fontSizeMobile` | string | Mobile font size |
| `fontWeight` | string | Font weight |
| `textTransform` | string | Text transform |
| `letterSpacing` | string | Letter spacing |

### Icon

| Attribute | Type | Description |
|-----------|------|-------------|
| `icon` | string | Icon HTML/class |
| `hasIcon` | boolean | Has icon enabled |
| `iconLocation` | string | Icon position (left, right) |
| `iconPadding` | string | Space between icon and text |
| `iconSize` | string | Icon size |

### Spacing

| Attribute | Type | Description |
|-----------|------|-------------|
| `paddingTop` | string | Top padding |
| `paddingRight` | string | Right padding |
| `paddingBottom` | string | Bottom padding |
| `paddingLeft` | string | Left padding |
| `marginTop` | string | Top margin |
| `marginRight` | string | Right margin |
| `marginBottom` | string | Bottom margin |
| `marginLeft` | string | Left margin |

### Border

| Attribute | Type | Description |
|-----------|------|-------------|
| `borderSizeTop` | string | Top border |
| `borderSizeRight` | string | Right border |
| `borderSizeBottom` | string | Bottom border |
| `borderSizeLeft` | string | Left border |
| `borderColor` | string | Border color |
| `borderColorHover` | string | Hover border color |
| `borderRadius` | string | Border radius |

## Headline Block Attributes

### Content

| Attribute | Type | Description |
|-----------|------|-------------|
| `content` | string | Headline text |
| `element` | string | HTML element (h1-h6, p, div) |

### Typography

| Attribute | Type | Description |
|-----------|------|-------------|
| `fontSize` | string | Font size |
| `fontSizeTablet` | string | Tablet font size |
| `fontSizeMobile` | string | Mobile font size |
| `fontFamily` | string | Font family |
| `fontWeight` | string | Font weight |
| `textTransform` | string | Text transform |
| `letterSpacing` | string | Letter spacing |
| `lineHeight` | string | Line height |
| `lineHeightTablet` | string | Tablet line height |
| `lineHeightMobile` | string | Mobile line height |
| `textAlign` | string | Text alignment |
| `textAlignTablet` | string | Tablet alignment |
| `textAlignMobile` | string | Mobile alignment |

### Colors

| Attribute | Type | Description |
|-----------|------|-------------|
| `textColor` | string | Text color |
| `linkColor` | string | Link color |
| `linkColorHover` | string | Link hover color |
| `backgroundColor` | string | Background color |
| `highlightTextColor` | string | Highlight text color |

### Icon

| Attribute | Type | Description |
|-----------|------|-------------|
| `icon` | string | Icon HTML |
| `hasIcon` | boolean | Icon enabled |
| `iconLocation` | string | Icon position |
| `iconVerticalAlignment` | string | Icon vertical align |
| `iconPadding` | string | Icon spacing |
| `iconSize` | string | Icon size |

## Image Block Attributes

### Media

| Attribute | Type | Description |
|-----------|------|-------------|
| `mediaId` | number | WordPress media ID |
| `mediaUrl` | string | Image URL |
| `altText` | string | Alt text |
| `title` | string | Title attribute |
| `sizeSlug` | string | Image size (full, large, medium, thumbnail) |

### Link

| Attribute | Type | Description |
|-----------|------|-------------|
| `href` | string | Link URL |
| `linkTarget` | string | Link target |
| `linkRel` | string | Link rel |
| `linkType` | string | Link type (custom, media, attachment) |

### Sizing

| Attribute | Type | Description |
|-----------|------|-------------|
| `width` | string | Image width |
| `height` | string | Image height |
| `objectFit` | string | Object fit |
| `objectPosition` | string | Object position |
| `alignment` | string | Block alignment |

### Effects (Pro)

| Attribute | Type | Description |
|-----------|------|-------------|
| `opacity` | number | Image opacity |
| `opacityHover` | number | Hover opacity |
| `filter` | string | CSS filter |
| `filterHover` | string | Hover filter |
| `transition` | string | Transition duration |

## Grid Block Attributes

### Layout

| Attribute | Type | Description |
|-----------|------|-------------|
| `columns` | number | Number of columns |
| `columnsTablet` | number | Tablet columns |
| `columnsMobile` | number | Mobile columns |
| `horizontalGap` | string | Column gap |
| `horizontalGapTablet` | string | Tablet column gap |
| `horizontalGapMobile` | string | Mobile column gap |
| `verticalGap` | string | Row gap |
| `verticalGapTablet` | string | Tablet row gap |
| `verticalGapMobile` | string | Mobile row gap |
| `horizontalAlignment` | string | Horizontal align |
| `verticalAlignment` | string | Vertical align |

## Query Loop Attributes (Pro)

| Attribute | Type | Description |
|-----------|------|-------------|
| `postType` | string | Post type to query |
| `postsPerPage` | number | Posts per page |
| `offset` | number | Posts to skip |
| `orderBy` | string | Order by field |
| `order` | string | Order direction (ASC, DESC) |
| `taxQuery` | array | Taxonomy query |
| `stickyPosts` | string | Sticky post handling |
| `excludeCurrent` | boolean | Exclude current post |
| `author` | number | Author ID |
| `postIn` | array | Specific post IDs |
| `postNotIn` | array | Exclude post IDs |
| `paginationType` | string | Pagination type |

### Tax Query Structure

```json
{
    "taxQuery": [
        {
            "taxonomy": "category",
            "terms": [1, 2, 3],
            "operator": "IN"
        },
        {
            "taxonomy": "post_tag",
            "terms": ["featured"],
            "field": "slug",
            "operator": "IN"
        }
    ],
    "taxQueryRelation": "AND"
}
```
