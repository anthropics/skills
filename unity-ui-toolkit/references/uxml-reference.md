# UXML Reference

Complete reference for Unity's UXML (Unity Extensible Markup Language) markup system.

## Document Structure

### Root Element

Every UXML document must have a root `<ui:UXML>` element with proper namespace declarations:

```xml
<ui:UXML
    xmlns:ui="UnityEngine.UIElements"
    xmlns:uie="UnityEditor.UIElements"
    xmlns:custom="YourNamespace.CustomControls">
    <!-- UI elements go here -->
</ui:UXML>
```

**Namespaces:**
- `xmlns:ui="UnityEngine.UIElements"` - Runtime UI Toolkit elements
- `xmlns:uie="UnityEditor.UIElements"` - Editor-only elements
- Custom namespaces for user-defined controls

### Editor Attributes

Special attributes available in Unity 6+:

```xml
<ui:UXML
    xmlns:ui="UnityEngine.UIElements"
    editor-extension-mode="True">
    <!-- Editor window/inspector UI -->
</ui:UXML>
```

## Common Attributes

These attributes apply to all visual elements:

### Identification and Styling

- `name` - Unique identifier (equivalent to HTML id)
- `class` - Space-separated class names for styling
- `style` - Inline USS styles (use sparingly)
- `picking-mode` - `Position` or `Ignore` (controls event detection)
- `tooltip` - Tooltip text shown on hover

### Visibility and Layout

- `visible` - Boolean, controls visibility
- `focusable` - Boolean, whether element can receive focus
- `tabindex` - Integer, order in tab navigation

### Example:
```xml
<ui:Button
    name="submit-btn"
    class="primary-button large"
    tooltip="Submit the form"
    focusable="true"
    tabindex="1" />
```

## Container Elements

### VisualElement

Base container for all UI elements. Can contain any child elements.

```xml
<ui:VisualElement name="container" class="main-container">
    <ui:Label text="Child content" />
    <ui:Button text="Click" />
</ui:VisualElement>
```

### ScrollView

Scrollable container with horizontal/vertical scrollbars.

**Attributes:**
- `mode` - `Vertical`, `Horizontal`, `VerticalAndHorizontal`
- `show-horizontal-scroller` - Boolean
- `show-vertical-scroller` - Boolean
- `horizontal-page-size` - Float
- `vertical-page-size` - Float
- `scroll-deceleration-rate` - Float (0-1)
- `elasticity` - Float

```xml
<ui:ScrollView mode="Vertical" show-horizontal-scroller="false">
    <ui:VisualElement style="height: 2000px;">
        <!-- Long content here -->
    </ui:VisualElement>
</ui:ScrollView>
```

### GroupBox

Container with optional label/header.

```xml
<ui:GroupBox text="Settings">
    <ui:Toggle label="Enable Sound" />
    <ui:Toggle label="Enable Music" />
</ui:GroupBox>
```

### Foldout

Collapsible container with header.

**Attributes:**
- `text` - Header text
- `value` - Boolean, expanded state

```xml
<ui:Foldout text="Advanced Options" value="false">
    <ui:Slider label="Volume" low-value="0" high-value="100" />
    <ui:Slider label="Brightness" low-value="0" high-value="100" />
</ui:Foldout>
```

### Box

Simple container with built-in styling.

```xml
<ui:Box>
    <ui:Label text="Content in a box" />
</ui:Box>
```

## Basic Controls

### Label

Displays non-editable text.

**Attributes:**
- `text` - Display text
- `enable-rich-text` - Boolean, enables rich text markup

```xml
<ui:Label text="Hello World" />
<ui:Label text="&lt;b&gt;Bold&lt;/b&gt; and &lt;i&gt;italic&lt;/i&gt;" enable-rich-text="true" />
```

### Button

Clickable button control.

**Attributes:**
- `text` - Button label

```xml
<ui:Button text="Click Me" name="action-button" />
```

### Toggle

Checkbox/toggle switch.

**Attributes:**
- `label` - Label text
- `value` - Boolean, checked state
- `text` - Alternative to label

```xml
<ui:Toggle label="Enable Feature" value="true" />
```

### TextField

Single-line text input.

**Attributes:**
- `label` - Label text
- `value` - Initial text value
- `max-length` - Integer, maximum character count
- `multiline` - Boolean, allow multiple lines
- `password` - Boolean, mask input characters
- `readonly` - Boolean, prevent editing
- `is-delayed` - Boolean, delay value change events

```xml
<ui:TextField
    label="Username"
    value=""
    max-length="20"
    placeholder-text="Enter username" />

<ui:TextField
    label="Password"
    password="true"
    value="" />

<ui:TextField
    label="Description"
    multiline="true"
    value=""
    style="height: 100px;" />
```

### IntegerField / FloatField / LongField / DoubleField

Numeric input fields.

**Attributes:**
- `label` - Label text
- `value` - Initial numeric value

```xml
<ui:IntegerField label="Age" value="25" />
<ui:FloatField label="Speed" value="1.5" />
<ui:LongField label="Large Number" value="1000000" />
<ui:DoubleField label="Precise Value" value="3.14159" />
```

### Vector2Field / Vector3Field / Vector4Field

Vector input fields (Unity types).

```xml
<ui:Vector2Field label="Position 2D" />
<ui:Vector3Field label="Position 3D" />
<ui:Vector4Field label="Quaternion" />
```

### BoundsField / BoundsIntField / RectField / RectIntField

Unity bounds and rect fields.

```xml
<ui:BoundsField label="Collider Bounds" />
<ui:RectField label="UI Rect" />
```

## Selection Controls

### DropdownField

Dropdown selection list.

**Attributes:**
- `label` - Label text
- `index` - Integer, selected index
- `choices` - Comma-separated list of options (limited use, prefer C# initialization)

```xml
<ui:DropdownField label="Difficulty" name="difficulty-dropdown" />
```

**Better approach in C#:**
```csharp
var dropdown = root.Q<DropdownField>("difficulty-dropdown");
dropdown.choices = new List<string> { "Easy", "Medium", "Hard" };
dropdown.index = 0;
```

### EnumField

Dropdown for C# enums (editor only typically).

```xml
<uie:EnumField label="Alignment" name="align-field" />
```

```csharp
var enumField = root.Q<EnumField>("align-field");
enumField.Init(TextAnchor.MiddleCenter);
```

### PopupField

Generic popup selection (similar to DropdownField).

```xml
<ui:PopupField label="Options" />
```

### RadioButton / RadioButtonGroup

Radio button selection (Unity 2021.2+).

```xml
<ui:RadioButtonGroup label="Size" value="1">
    <ui:RadioButton label="Small" />
    <ui:RadioButton label="Medium" />
    <ui:RadioButton label="Large" />
</ui:RadioButtonGroup>
```

## Value Controls

### Slider / SliderInt

Horizontal slider for numeric values.

**Attributes:**
- `label` - Label text
- `low-value` - Minimum value
- `high-value` - Maximum value
- `value` - Current value
- `show-input-field` - Boolean, show text input
- `page-size` - Float, keyboard increment
- `direction` - `Horizontal` or `Vertical`

```xml
<ui:Slider
    label="Volume"
    low-value="0"
    high-value="100"
    value="75"
    show-input-field="true" />

<ui:SliderInt
    label="Quality"
    low-value="0"
    high-value="5"
    value="3" />
```

### MinMaxSlider

Dual-handle range slider.

**Attributes:**
- `label` - Label text
- `min-value` - Minimum allowed value
- `max-value` - Maximum allowed value
- `low-limit` - Current low value
- `high-limit` - Current high value

```xml
<ui:MinMaxSlider
    label="Price Range"
    min-value="0"
    max-value="1000"
    low-limit="100"
    high-limit="500" />
```

### ProgressBar

Visual progress indicator.

**Attributes:**
- `title` - Label text
- `low-value` - Minimum value (typically 0)
- `high-value` - Maximum value (typically 100)
- `value` - Current progress value

```xml
<ui:ProgressBar
    title="Loading..."
    low-value="0"
    high-value="100"
    value="45" />
```

## List and Tree Controls

### ListView

Efficient scrollable list with item virtualization.

**Attributes:**
- `show-border` - Boolean
- `selection-type` - `None`, `Single`, `Multiple`
- `show-alternating-row-backgrounds` - `None`, `All`, `ContentOnly`
- `reorderable` - Boolean, allow drag reordering
- `show-bound-collection-size` - Boolean
- `horizontal-scrolling` - Boolean
- `item-height` - Integer, fixed item height

```xml
<ui:ListView
    name="item-list"
    show-border="true"
    selection-type="Single"
    show-alternating-row-backgrounds="ContentOnly"
    reorderable="true" />
```

**Setup in C#:**
```csharp
var listView = root.Q<ListView>("item-list");
listView.makeItem = () => new Label();
listView.bindItem = (element, index) =>
{
    (element as Label).text = $"Item {index}";
};
listView.itemsSource = new List<string> { "Item 1", "Item 2", "Item 3" };
```

### TreeView

Hierarchical tree control.

```xml
<ui:TreeView name="hierarchy-tree" />
```

## Editor-Only Controls

These require `xmlns:uie="UnityEditor.UIElements"`:

### ObjectField

Unity object reference picker.

**Attributes:**
- `label` - Label text
- `type` - Object type (as string, e.g., "UnityEngine.GameObject")
- `allow-scene-objects` - Boolean

```xml
<uie:ObjectField
    label="Prefab"
    type="UnityEngine.GameObject"
    allow-scene-objects="false" />
```

### LayerField / LayerMaskField / TagField

Unity layer and tag selectors.

```xml
<uie:LayerField label="Layer" />
<uie:LayerMaskField label="Layer Mask" />
<uie:TagField label="Tag" />
```

### ColorField

Color picker.

**Attributes:**
- `label` - Label text
- `show-eye-dropper` - Boolean
- `show-alpha` - Boolean
- `hdr` - Boolean, High Dynamic Range

```xml
<uie:ColorField
    label="Background Color"
    show-alpha="true"
    hdr="false" />
```

### CurveField / GradientField

Animation curve and gradient editors.

```xml
<uie:CurveField label="Animation Curve" />
<uie:GradientField label="Color Gradient" />
```

### PropertyField

Automatic field for SerializedProperty (most flexible editor field).

```xml
<uie:PropertyField name="my-property" />
```

## Templates and Reusability

### Template Definition

Define reusable UI templates:

```xml
<ui:UXML xmlns:ui="UnityEngine.UIElements">
    <ui:Template name="PlayerCard" src="PlayerCardTemplate.uxml" />

    <ui:VisualElement>
        <ui:Instance template="PlayerCard" />
        <ui:Instance template="PlayerCard" />
    </ui:VisualElement>
</ui:UXML>
```

### Template File (PlayerCardTemplate.uxml)

```xml
<ui:UXML xmlns:ui="UnityEngine.UIElements">
    <ui:VisualElement class="player-card">
        <ui:Label name="player-name" text="Player Name" />
        <ui:Label name="player-score" text="Score: 0" />
    </ui:VisualElement>
</ui:UXML>
```

### Template Instantiation in C#

```csharp
var template = AssetDatabase.LoadAssetAtPath<VisualTreeAsset>("Assets/UI/PlayerCard.uxml");
var instance = template.Instantiate();
root.Add(instance);
```

## Binding

### Data Binding Attributes

Bind UI elements to data sources:

```xml
<ui:TextField label="Player Name" binding-path="playerName" />
<ui:IntegerField label="Score" binding-path="score" />
```

**C# Setup:**
```csharp
var serializedObject = new SerializedObject(targetObject);
root.Bind(serializedObject);
```

## Style Attribute

Inline USS styles (use sparingly, prefer USS files):

```xml
<ui:Button
    text="Styled Button"
    style="
        background-color: rgb(100, 150, 200);
        color: white;
        width: 200px;
        height: 50px;
        border-radius: 10px;
        margin: 5px;
    " />
```

**Better approach:** Use USS classes:

```xml
<ui:Button text="Styled Button" class="primary-button" />
```

## Custom Controls in UXML

Register custom controls for use in UXML:

**C# Custom Control:**
```csharp
public class CustomButton : Button
{
    public new class UxmlFactory : UxmlFactory<CustomButton, UxmlTraits> { }

    public new class UxmlTraits : Button.UxmlTraits
    {
        UxmlStringAttributeDescription iconPath = new UxmlStringAttributeDescription
        {
            name = "icon-path"
        };

        public override void Init(VisualElement ve, IUxmlAttributes bag, CreationContext cc)
        {
            base.Init(ve, bag, cc);
            var button = ve as CustomButton;
            button.SetIcon(iconPath.GetValueFromBag(bag, cc));
        }
    }

    public void SetIcon(string path)
    {
        // Load and set icon
    }
}
```

**UXML Usage:**
```xml
<ui:UXML xmlns:ui="UnityEngine.UIElements" xmlns:custom="MyNamespace">
    <custom:CustomButton text="Custom" icon-path="Assets/Icons/star.png" />
</ui:UXML>
```

## Best Practices

1. **Use Templates for Reusability**: Extract common UI patterns into templates
2. **Minimize Inline Styles**: Use USS classes instead of style attributes
3. **Semantic Naming**: Use clear, descriptive names for elements
4. **Keep Structure Clean**: Organize hierarchy logically
5. **Separate Concerns**: UXML for structure, USS for style, C# for logic
6. **Use Proper Namespaces**: Include only needed xmlns declarations
7. **Validate XML**: Ensure proper nesting and closing tags
8. **Comment Complex Structures**: Use XML comments `<!-- comment -->`

## Common Patterns

### Form Layout

```xml
<ui:VisualElement class="form-container">
    <ui:TextField label="Name" name="name-field" />
    <ui:TextField label="Email" name="email-field" />
    <ui:IntegerField label="Age" name="age-field" />
    <ui:DropdownField label="Country" name="country-field" />
    <ui:Button text="Submit" name="submit-button" />
</ui:VisualElement>
```

### Card Grid

```xml
<ui:ScrollView>
    <ui:VisualElement class="card-grid">
        <ui:VisualElement class="card">
            <ui:Label text="Card 1" class="card-title" />
        </ui:VisualElement>
        <ui:VisualElement class="card">
            <ui:Label text="Card 2" class="card-title" />
        </ui:VisualElement>
        <!-- More cards -->
    </ui:VisualElement>
</ui:ScrollView>
```

### Header with Navigation

```xml
<ui:VisualElement class="header">
    <ui:Label text="My Application" class="header-title" />
    <ui:VisualElement class="nav-buttons">
        <ui:Button text="Home" class="nav-button" />
        <ui:Button text="Settings" class="nav-button" />
        <ui:Button text="About" class="nav-button" />
    </ui:VisualElement>
</ui:VisualElement>
```

## Troubleshooting

**Elements not appearing:**
- Check namespace declarations
- Verify parent element size (elements need space to render)
- Check `visible` and `display` properties
- Ensure USS files are loaded

**Binding not working:**
- Verify `binding-path` matches property name exactly
- Ensure `Bind()` is called on root or parent element
- Check SerializedObject is created correctly

**Templates not found:**
- Verify file path in `src` attribute
- Ensure template file has proper UXML structure
- Check for circular template references
