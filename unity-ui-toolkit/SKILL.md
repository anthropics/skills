---
name: unity-ui-toolkit
description: This skill should be used when working with Unity 6.2 UI Toolkit (UIElements) for creating user interfaces, including UXML structure, USS styling, C# scripting, visual elements, event handling, data binding, and UI Builder workflows. Use this skill for runtime UI, editor extensions, debugging UI, and any UI-related development in Unity projects.
---

# Unity UI Toolkit

## Overview

Unity UI Toolkit is a collection of features, resources, and tools for developing user interfaces in Unity 6.2. It provides a retained-mode UI system based on web technologies, using UXML for structure (similar to HTML), USS for styling (similar to CSS), and C# for logic. UI Toolkit is suitable for both runtime game UI and Unity Editor extensions.

This skill provides comprehensive guidance for creating, styling, and scripting UI Toolkit interfaces, working with the UI Builder visual editor, handling events, implementing data binding, and following best practices for performance and maintainability.

## Core Capabilities

### 1. UXML Structure (UI Markup)

UXML (Unity Extensible Markup Language) defines the structure and hierarchy of UI elements.

**Key concepts:**
- UXML files are XML-based text files with `.uxml` extension
- Elements are defined using tags (e.g., `<Button>`, `<Label>`, `<VisualElement>`)
- Support templates and inheritance for reusability
- Can be edited in text editors or UI Builder

**Basic UXML structure:**
```xml
<ui:UXML xmlns:ui="UnityEngine.UIElements" xmlns:uie="UnityEditor.UIElements">
    <ui:VisualElement name="root" class="container">
        <ui:Label text="Hello World" name="title-label" />
        <ui:Button text="Click Me" name="action-button" />
    </ui:VisualElement>
</ui:UXML>
```

**When to use UXML:**
- Defining static UI structure
- Creating reusable UI templates
- Separating UI layout from logic
- Working with UI Builder for visual editing

**Loading UXML in C#:**
```csharp
// Method 1: Direct reference
var visualTree = AssetDatabase.LoadAssetAtPath<VisualTreeAsset>("Assets/UI/MyUI.uxml");
var root = visualTree.Instantiate();

// Method 2: Resources folder
var visualTree = Resources.Load<VisualTreeAsset>("MyUI");
var root = visualTree.Instantiate();
```

### 2. USS Styling (Style Sheets)

USS (Unity Style Sheets) applies visual styles and layout rules to UI elements.

**Key concepts:**
- USS files are text files with `.uss` extension
- Syntax similar to CSS with Unity-specific properties
- Supports selectors: element type, class, name, pseudo-classes
- Cascading and specificity rules apply
- Inline styles override stylesheet styles

**USS syntax examples:**
```css
/* Type selector */
Button {
    background-color: rgb(50, 150, 200);
    color: white;
    border-radius: 5px;
    padding: 10px;
}

/* Class selector */
.primary-button {
    background-color: rgb(0, 120, 215);
    font-size: 16px;
}

/* Name selector */
#submit-button {
    width: 200px;
    height: 50px;
}

/* Pseudo-class */
Button:hover {
    background-color: rgb(70, 170, 220);
}

/* Descendant selector */
.container Label {
    margin: 5px;
}
```

**Common USS properties:**
- Layout: `width`, `height`, `margin`, `padding`, `flex-direction`, `align-items`, `justify-content`
- Visual: `background-color`, `border-color`, `border-width`, `border-radius`, `opacity`
- Text: `color`, `font-size`, `-unity-font`, `-unity-font-style`, `-unity-text-align`
- Display: `display`, `visibility`, `overflow`, `position` (absolute/relative)

**Best practices:**
- Use USS files instead of inline styles for better performance and maintainability
- Follow BEM (Block Element Modifier) naming convention for classes
- Organize styles hierarchically
- Use CSS custom properties (variables) for theming

**Loading USS in C#:**
```csharp
var styleSheet = AssetDatabase.LoadAssetAtPath<StyleSheet>("Assets/UI/Styles.uss");
rootVisualElement.styleSheets.Add(styleSheet);
```

### 3. C# Scripting and Visual Elements

Create and manipulate UI elements programmatically using C# scripts.

**Common visual elements:**
- **Containers:** `VisualElement`, `ScrollView`, `ListView`, `TreeView`, `GroupBox`, `Foldout`
- **Controls:** `Button`, `Toggle`, `TextField`, `Label`, `Slider`, `DropdownField`, `EnumField`
- **Custom:** Create custom controls by inheriting from `VisualElement`

**Creating elements in C#:**
```csharp
using UnityEngine;
using UnityEngine.UIElements;

public class UIController : MonoBehaviour
{
    private void OnEnable()
    {
        var root = GetComponent<UIDocument>().rootVisualElement;

        // Create elements
        var container = new VisualElement();
        container.AddToClassList("main-container");

        var label = new Label("Score: 0");
        label.name = "score-label";

        var button = new Button(() => OnButtonClick());
        button.text = "Start Game";

        // Build hierarchy
        container.Add(label);
        container.Add(button);
        root.Add(container);
    }

    private void OnButtonClick()
    {
        Debug.Log("Button clicked!");
    }
}
```

**Querying elements:**
```csharp
// By name (ID)
var element = root.Q<Button>("my-button");

// By class
var elements = root.Query<Label>(className: "score-text").ToList();

// By type
var allButtons = root.Query<Button>().ToList();

// Complex query
var element = root.Q<VisualElement>("container").Q<Label>("title");
```

**Manipulating styles in C#:**
```csharp
// Direct style manipulation
element.style.backgroundColor = new Color(0.2f, 0.5f, 0.8f);
element.style.width = 200;
element.style.height = Length.Percent(50);

// Add/remove classes
element.AddToClassList("active");
element.RemoveFromClassList("inactive");
element.ToggleInClassList("highlighted");
```

### 4. Event Handling

Handle user interactions and UI events using callbacks and event registration.

**Event types:**
- **Mouse:** `MouseDownEvent`, `MouseUpEvent`, `MouseMoveEvent`, `MouseEnterEvent`, `MouseLeaveEvent`, `WheelEvent`
- **Click:** `ClickEvent`, `PointerDownEvent`, `PointerUpEvent`, `PointerMoveEvent`
- **Keyboard:** `KeyDownEvent`, `KeyUpEvent`
- **Navigation:** `NavigationMoveEvent`, `NavigationSubmitEvent`, `NavigationCancelEvent`
- **Change:** `ChangeEvent<T>`, `InputEvent`
- **Focus:** `FocusInEvent`, `FocusOutEvent`, `BlurEvent`

**Registering callbacks:**
```csharp
// Method 1: RegisterCallback
button.RegisterCallback<ClickEvent>(OnButtonClicked);

void OnButtonClicked(ClickEvent evt)
{
    Debug.Log($"Button clicked at position: {evt.position}");
}

// Method 2: Using clickable property (Button-specific)
button.clicked += () => Debug.Log("Button clicked!");

// Method 3: ChangeEvent for value changes
var textField = root.Q<TextField>("name-input");
textField.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Value changed from {evt.previousValue} to {evt.newValue}");
});
```

**Event propagation:**
```csharp
// Register in trickle-down phase (before target)
element.RegisterCallback<ClickEvent>(OnClick, TrickleDown.TrickleDown);

// Register in bubble-up phase (after target) - default
element.RegisterCallback<ClickEvent>(OnClick, TrickleDown.NoTrickleDown);

// Stop propagation
void OnClick(ClickEvent evt)
{
    evt.StopPropagation(); // Stops further propagation
    evt.PreventDefault();  // Prevents default behavior
}

// Unregister callback
element.UnregisterCallback<ClickEvent>(OnButtonClicked);
```

### 5. UI Builder

Visual editor for creating and editing UXML and USS files.

**Access:** Window > UI Toolkit > UI Builder

**Key features:**
- Drag-and-drop UI element creation
- Visual hierarchy editing
- Real-time style editing with USS selector management
- UXML template creation and instantiation
- Preview mode for testing
- Inspector for element properties and styles

**Workflow:**
1. Create new UXML document or open existing
2. Add elements from Library panel
3. Arrange elements in Hierarchy panel
4. Style with StyleSheets panel or Inspector
5. Save UXML and USS files
6. Load in runtime or editor code

**Best practices:**
- Use UI Builder for initial layout and structure
- Create reusable templates for common patterns
- Organize USS selectors in StyleSheets panel
- Use preview mode to test responsive behavior
- Switch to code for complex logic and dynamic content

### 6. Data Binding (Unity 6+)

Bind UI elements to data sources for automatic updates.

**Key concepts:**
- `BindingPath`: Specifies property to bind
- `IBindable`: Interface for bindable elements
- `SerializedObject`: Data source for binding
- `Bind()` and `Unbind()`: Methods for managing bindings

**Example with SerializedObject:**
```csharp
[SerializeField] private int score;
[SerializeField] private string playerName;

private void OnEnable()
{
    var root = GetComponent<UIDocument>().rootVisualElement;

    // Create serialized object
    var serializedObject = new SerializedObject(this);

    // Bind elements
    var scoreField = root.Q<IntegerField>("score-field");
    scoreField.bindingPath = "score";
    scoreField.Bind(serializedObject);

    var nameField = root.Q<TextField>("name-field");
    nameField.bindingPath = "playerName";
    nameField.Bind(serializedObject);
}
```

**Custom data binding:**
```csharp
public class CustomDataSource
{
    public int Value { get; set; }
}

// Manual binding
var dataSource = new CustomDataSource { Value = 100 };
var label = root.Q<Label>("value-label");

void UpdateLabel()
{
    label.text = $"Value: {dataSource.Value}";
}

// Call UpdateLabel() whenever data changes
```

## Common Workflows

### Creating a New Runtime UI

1. **Create UI Document:**
   - Create GameObject in scene
   - Add `UI Document` component
   - Set `Panel Settings` (Create > UI Toolkit > Panel Settings Asset)

2. **Design UI structure:**
   - Open UI Builder (Window > UI Toolkit > UI Builder)
   - Create UXML document
   - Add and arrange visual elements
   - Save UXML file

3. **Style the UI:**
   - In UI Builder StyleSheets panel, create USS file
   - Add selectors and properties
   - Or write USS directly in text editor
   - Assign to UXML document

4. **Add interactivity:**
   - Create C# MonoBehaviour script
   - Get root element: `GetComponent<UIDocument>().rootVisualElement`
   - Query elements and register callbacks
   - Attach script to UI Document GameObject

5. **Test and iterate:**
   - Enter Play mode
   - Use UI Toolkit Debugger (Window > UI Toolkit > Debugger)
   - Adjust UXML, USS, and C# as needed

### Creating a Custom Control

1. **Create C# class inheriting from VisualElement:**
```csharp
using UnityEngine.UIElements;

public class HealthBar : VisualElement
{
    private VisualElement fillElement;
    private Label valueLabel;

    private float maxHealth = 100f;
    private float currentHealth = 100f;

    // UxmlFactory enables use in UI Builder
    public new class UxmlFactory : UxmlFactory<HealthBar, UxmlTraits> { }

    public new class UxmlTraits : VisualElement.UxmlTraits
    {
        UxmlFloatAttributeDescription maxHealthAttr = new UxmlFloatAttributeDescription
        {
            name = "max-health",
            defaultValue = 100f
        };

        public override void Init(VisualElement ve, IUxmlAttributes bag, CreationContext cc)
        {
            base.Init(ve, bag, cc);
            var healthBar = ve as HealthBar;
            healthBar.maxHealth = maxHealthAttr.GetValueFromBag(bag, cc);
            healthBar.currentHealth = healthBar.maxHealth;
        }
    }

    public HealthBar()
    {
        // Add USS class for styling
        AddToClassList("health-bar");

        // Create child elements
        fillElement = new VisualElement();
        fillElement.AddToClassList("health-bar__fill");

        valueLabel = new Label("100/100");
        valueLabel.AddToClassList("health-bar__label");

        Add(fillElement);
        Add(valueLabel);

        UpdateDisplay();
    }

    public void SetHealth(float current, float max)
    {
        currentHealth = Mathf.Clamp(current, 0, max);
        maxHealth = max;
        UpdateDisplay();
    }

    private void UpdateDisplay()
    {
        float percentage = (currentHealth / maxHealth) * 100f;
        fillElement.style.width = Length.Percent(percentage);
        valueLabel.text = $"{currentHealth:F0}/{maxHealth:F0}";
    }
}
```

2. **Create USS for custom control:**
```css
.health-bar {
    width: 200px;
    height: 30px;
    background-color: rgb(50, 50, 50);
    border-radius: 5px;
    overflow: hidden;
}

.health-bar__fill {
    height: 100%;
    background-color: rgb(0, 200, 0);
    transition-duration: 0.3s;
}

.health-bar__label {
    position: absolute;
    width: 100%;
    height: 100%;
    -unity-text-align: middle-center;
    color: white;
}
```

3. **Use in UXML or C#:**
```xml
<!-- In UXML (requires namespace) -->
<HealthBar max-health="150" />
```

```csharp
// In C#
var healthBar = new HealthBar();
healthBar.SetHealth(75, 100);
root.Add(healthBar);
```

### Debugging and Optimization

**UI Toolkit Debugger:**
- Access: Window > UI Toolkit > Debugger
- Select UI panel to inspect
- View element hierarchy and styles
- See computed styles and layout
- Identify performance issues

**Performance best practices:**
- Minimize layout recalculations (avoid frequent style changes)
- Use USS instead of inline styles
- Pool and reuse elements for dynamic lists
- Use `ListView` for large scrollable lists
- Avoid deep nesting of elements
- Use `display: none` instead of removing elements for better performance

**Common issues:**
- **Element not appearing:** Check `display` property, parent visibility, and z-index
- **Styles not applying:** Verify USS selector specificity and file loading
- **Events not firing:** Check element is pickable and has correct event registration
- **Layout issues:** Use Flexbox properties correctly (`flex-direction`, `align-items`, `justify-content`)

## Editor Extensions

UI Toolkit is commonly used for creating custom Unity Editor windows and inspectors.

**Create custom editor window:**
```csharp
using UnityEditor;
using UnityEngine.UIElements;

public class MyEditorWindow : EditorWindow
{
    [MenuItem("Window/My Custom Window")]
    public static void ShowWindow()
    {
        GetWindow<MyEditorWindow>("My Window");
    }

    public void CreateGUI()
    {
        var root = rootVisualElement;

        // Load UXML
        var visualTree = AssetDatabase.LoadAssetAtPath<VisualTreeAsset>(
            "Assets/Editor/MyWindow.uxml"
        );
        visualTree.CloneTree(root);

        // Setup elements
        var button = root.Q<Button>("refresh-button");
        button.clicked += OnRefreshClicked;
    }

    private void OnRefreshClicked()
    {
        // Handle button click
    }
}
```

**Custom inspector:**
```csharp
using UnityEditor;
using UnityEditor.UIElements;
using UnityEngine.UIElements;

[CustomEditor(typeof(MyComponent))]
public class MyComponentEditor : Editor
{
    public override VisualElement CreateInspectorGUI()
    {
        var root = new VisualElement();

        // Load UXML (optional)
        var visualTree = AssetDatabase.LoadAssetAtPath<VisualTreeAsset>(
            "Assets/Editor/MyComponentInspector.uxml"
        );
        visualTree.CloneTree(root);

        // Bind to serialized properties
        var scoreField = root.Q<IntegerField>("score");
        scoreField.bindingPath = "score";

        return root;
    }
}
```

## Resources

This skill includes comprehensive reference documentation:

### references/

- **uxml-reference.md**: Complete UXML element reference with all built-in elements, attributes, and examples
- **uss-reference.md**: Complete USS property reference with all supported CSS properties and Unity-specific extensions
- **visual-elements-reference.md**: Detailed guide to all built-in visual elements (controls, containers, etc.) with code examples
- **events-reference.md**: Comprehensive event handling guide with all event types and propagation details
- **best-practices.md**: Performance optimization, architecture patterns, and common pitfalls to avoid

### assets/

- **templates/**: Common UI templates (HUD, menu, dialog, inventory grid, etc.)
- **common-styles.uss**: Reusable USS components and utility classes

## Quick Reference

**File extensions:**
- `.uxml` - UI structure/markup files
- `.uss` - Style sheet files
- `.cs` - C# scripts for logic

**Key namespaces:**
```csharp
using UnityEngine.UIElements;           // Runtime UI Toolkit
using UnityEditor.UIElements;           // Editor-only controls
using UnityEngine.UIElements.Experimental; // Experimental features
```

**Essential components:**
- `UIDocument` - Component to display UI in scene
- `PanelSettings` - Configuration for UI rendering
- `VisualTreeAsset` - UXML file asset reference
- `StyleSheet` - USS file asset reference

**Common element types to remember:**
- `VisualElement` - Base container
- `Button`, `Toggle`, `TextField`, `Label` - Basic controls
- `ScrollView`, `ListView` - Scrollable containers
- `Slider`, `SliderInt`, `MinMaxSlider` - Value controls
- `DropdownField`, `EnumField`, `PopupField` - Selection controls

## When to Use UI Toolkit vs UGUI

**Use UI Toolkit for:**
- Editor extensions and tools
- Complex UI with many elements
- Modern, responsive designs
- UI requiring extensive styling
- Unity 6+ projects prioritizing performance

**Use UGUI for:**
- Legacy project compatibility
- 3D world-space UI with complex interactions
- Projects requiring specific UGUI features
- Teams familiar with UGUI workflow

**Note:** Both systems can coexist in the same project if needed.
