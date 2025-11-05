# Visual Elements Reference

Comprehensive guide to all built-in UI Toolkit visual elements with code examples.

## Base Classes

### VisualElement

The base class for all UI elements. Can serve as a generic container.

**Key Properties:**
```csharp
// Hierarchy
visualElement.Add(childElement);
visualElement.Remove(childElement);
visualElement.Clear(); // Remove all children
visualElement.parent;
visualElement.hierarchy.childCount;
visualElement.hierarchy[index];

// Styling
visualElement.style.width = 200;
visualElement.style.height = 100;
visualElement.AddToClassList("my-class");
visualElement.RemoveFromClassList("my-class");
visualElement.ToggleInClassList("active");
visualElement.EnableInClassList("highlight", true);

// Layout
visualElement.layout; // Rect (read-only, computed after layout)
visualElement.worldBound; // Rect in screen space
visualElement.localBound; // Rect in local space

// State
visualElement.visible = true;
visualElement.SetEnabled(true);
visualElement.pickingMode = PickingMode.Position;
visualElement.focusable = true;

// Events
visualElement.RegisterCallback<ClickEvent>(OnClick);
visualElement.UnregisterCallback<ClickEvent>(OnClick);

// Query
var element = visualElement.Q<Button>("button-name");
var elements = visualElement.Query<Label>(className: "score").ToList();
```

**Example:**
```csharp
var container = new VisualElement();
container.name = "main-container";
container.AddToClassList("container");
container.style.flexDirection = FlexDirection.Column;
container.style.alignItems = Align.Center;

var label = new Label("Hello");
container.Add(label);
```

### BindableElement

Base class for elements that support data binding.

```csharp
var field = new TextField();
field.bindingPath = "playerName";
field.Bind(serializedObject);
```

## Containers

### Box

Simple container with built-in box styling.

```csharp
var box = new Box();
box.Add(new Label("Content"));
```

### ScrollView

Scrollable container with scrollbars.

**Constructor:**
```csharp
var scrollView = new ScrollView();
var scrollView = new ScrollView(ScrollViewMode.Vertical);
var scrollView = new ScrollView(ScrollViewMode.Horizontal);
var scrollView = new ScrollView(ScrollViewMode.VerticalAndHorizontal);
```

**Properties:**
```csharp
scrollView.mode = ScrollViewMode.Vertical;
scrollView.showHorizontal = false;
scrollView.showVertical = true;
scrollView.horizontalPageSize = 100;
scrollView.verticalPageSize = 100;
scrollView.scrollOffset = new Vector2(0, 100); // Scroll position
scrollView.elasticity = 0.1f;
```

**Methods:**
```csharp
scrollView.ScrollTo(childElement);
```

**Example:**
```csharp
var scrollView = new ScrollView(ScrollViewMode.Vertical);
scrollView.style.height = 400;

for (int i = 0; i < 100; i++)
{
    scrollView.Add(new Label($"Item {i}"));
}
```

### GroupBox

Container with optional header label.

```csharp
var group = new GroupBox("Settings");
group.Add(new Toggle("Enable Sound"));
group.Add(new Toggle("Enable Music"));
```

### Foldout

Collapsible container with toggle header.

```csharp
var foldout = new Foldout();
foldout.text = "Advanced Options";
foldout.value = false; // Collapsed by default

foldout.Add(new Slider("Volume", 0, 100));
foldout.Add(new Slider("Brightness", 0, 100));

// Listen for toggle
foldout.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Foldout {(evt.newValue ? "expanded" : "collapsed")}");
});
```

### TwoPaneSplitView

Resizable split view with two panes.

```csharp
var splitView = new TwoPaneSplitView(
    0,                              // index of fixed pane
    250,                            // fixed pane initial size
    TwoPaneSplitViewOrientation.Horizontal
);

var leftPane = new VisualElement();
var rightPane = new VisualElement();

splitView.Add(leftPane);
splitView.Add(rightPane);
```

## Text Elements

### Label

Non-editable text display.

```csharp
var label = new Label();
label.text = "Hello World";

// Or with constructor
var label = new Label("Hello World");

// Enable rich text
label.enableRichText = true;
label.text = "<b>Bold</b> and <i>italic</i>";

// Multiline
label.style.whiteSpace = WhiteSpace.Normal;
```

### TextField

Single or multi-line text input.

**Constructor:**
```csharp
var textField = new TextField();
var textField = new TextField("Label:");
var textField = new TextField("Label:", 50, false, false, '*'); // maxLength, multiline, isDelayed, maskChar
```

**Properties:**
```csharp
textField.label = "Name:";
textField.value = "John Doe";
textField.maxLength = 50;
textField.isReadOnly = false;
textField.isDelayed = false; // Delay value change events until focus lost
textField.maskChar = '\0'; // Password masking (use '*' for password)
textField.isPasswordField = true; // Convenience for maskChar
```

**Events:**
```csharp
textField.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Text changed: {evt.previousValue} -> {evt.newValue}");
});

textField.RegisterCallback<FocusOutEvent>(evt =>
{
    Debug.Log("Focus lost");
});
```

**Multiline:**
```csharp
var multiline = new TextField();
multiline.multiline = true;
multiline.style.height = 100;
multiline.style.whiteSpace = WhiteSpace.Normal;
```

## Buttons

### Button

Standard clickable button.

```csharp
// Constructor with callback
var button = new Button(() => Debug.Log("Clicked!"));
button.text = "Click Me";

// Or set callback later
var button = new Button();
button.text = "Submit";
button.clicked += OnSubmit;

void OnSubmit()
{
    Debug.Log("Submit clicked");
}

// Or use events
button.RegisterCallback<ClickEvent>(evt =>
{
    Debug.Log($"Clicked at {evt.position}");
});
```

### RepeatButton

Button that triggers repeatedly while held.

```csharp
var repeatButton = new RepeatButton(() =>
{
    Debug.Log("Triggered every delay interval");
}, 100, 30); // delay (ms), interval (ms)

repeatButton.text = "Hold Me";
```

## Toggle and Selection

### Toggle

Checkbox/toggle control.

```csharp
var toggle = new Toggle();
toggle.label = "Enable Feature";
toggle.value = true;

toggle.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Toggle: {evt.newValue}");
});
```

### RadioButton

Single radio button (use RadioButtonGroup for groups).

```csharp
var radio = new RadioButton();
radio.text = "Option A";
```

### RadioButtonGroup

Group of radio buttons (single selection).

```csharp
var group = new RadioButtonGroup();
group.label = "Size";
group.choices = new List<string> { "Small", "Medium", "Large" };
group.value = 0; // Selected index

group.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Selected: {group.choices[evt.newValue]}");
});
```

## Numeric Fields

### IntegerField

Integer number input.

```csharp
var intField = new IntegerField();
intField.label = "Age";
intField.value = 25;

intField.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Value: {evt.newValue}");
});

// Or in constructor
var intField = new IntegerField("Age:", 2); // label, maxLength
```

### FloatField

Floating-point number input.

```csharp
var floatField = new FloatField("Speed:");
floatField.value = 1.5f;
```

### LongField

Long integer input.

```csharp
var longField = new LongField("Population:");
longField.value = 1000000L;
```

### DoubleField

Double-precision floating-point input.

```csharp
var doubleField = new DoubleField("Precise:");
doubleField.value = 3.14159265359;
```

### Vector2Field, Vector3Field, Vector4Field

Vector input fields.

```csharp
var vec2 = new Vector2Field("Position 2D");
vec2.value = new Vector2(10, 20);

var vec3 = new Vector3Field("Position 3D");
vec3.value = new Vector3(1, 2, 3);

var vec4 = new Vector4Field("Rotation");
vec4.value = new Vector4(0, 0, 0, 1);
```

### Vector2IntField, Vector3IntField

Integer vector fields.

```csharp
var vec2Int = new Vector2IntField("Grid Position");
vec2Int.value = new Vector2Int(5, 10);

var vec3Int = new Vector3IntField("Chunk Coord");
vec3Int.value = new Vector3Int(0, 0, 0);
```

### RectField, RectIntField

Rectangle fields.

```csharp
var rectField = new RectField("Area");
rectField.value = new Rect(0, 0, 100, 100);

var rectIntField = new RectIntField("Tile Rect");
rectIntField.value = new RectInt(0, 0, 16, 16);
```

### BoundsField, BoundsIntField

Bounds fields (min/max 3D coordinates).

```csharp
var boundsField = new BoundsField("Collider Bounds");
boundsField.value = new Bounds(Vector3.zero, Vector3.one);

var boundsIntField = new BoundsIntField("Grid Bounds");
boundsIntField.value = new BoundsInt(Vector3Int.zero, Vector3Int.one);
```

## Sliders and Progress

### Slider

Horizontal or vertical slider for float values.

```csharp
var slider = new Slider();
slider.label = "Volume";
slider.lowValue = 0;
slider.highValue = 100;
slider.value = 75;
slider.showInputField = true; // Show text input

slider.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Volume: {evt.newValue}");
});

// Vertical slider
slider.direction = SliderDirection.Vertical;
```

### SliderInt

Integer slider.

```csharp
var sliderInt = new SliderInt("Quality", 0, 5);
sliderInt.value = 3;
sliderInt.showInputField = true;
```

### MinMaxSlider

Dual-handle range slider.

```csharp
var minMax = new MinMaxSlider();
minMax.label = "Price Range";
minMax.minValue = 0;
minMax.maxValue = 1000;
minMax.lowLimit = 100;  // Current low value
minMax.highLimit = 500; // Current high value

minMax.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Range: {evt.newValue.x} - {evt.newValue.y}");
});
```

### ProgressBar

Visual progress indicator.

```csharp
var progress = new ProgressBar();
progress.title = "Loading...";
progress.lowValue = 0;
progress.highValue = 100;
progress.value = 45;

// Indeterminate progress (animated)
progress.value = float.NaN; // Not supported by default, needs custom styling
```

## Dropdown and Selection

### DropdownField

Dropdown selection menu.

```csharp
var dropdown = new DropdownField();
dropdown.label = "Difficulty";
dropdown.choices = new List<string> { "Easy", "Medium", "Hard" };
dropdown.value = "Medium"; // Selected value (string)
dropdown.index = 1;        // Selected index

dropdown.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Selected: {evt.newValue}");
});

// With constructor
var dropdown = new DropdownField(
    "Difficulty",
    new List<string> { "Easy", "Medium", "Hard" },
    0 // default index
);
```

### EnumField

Dropdown for C# enums (Editor namespace).

```csharp
using UnityEditor.UIElements;

var enumField = new EnumField("Alignment");
enumField.Init(TextAnchor.MiddleCenter);

enumField.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Selected: {evt.newValue}");
});

// Get enum value
TextAnchor alignment = (TextAnchor)enumField.value;
```

### PopupField\<T>

Generic popup field.

```csharp
var options = new List<string> { "Red", "Green", "Blue" };
var popup = new PopupField<string>("Color", options, 0);

popup.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Color: {evt.newValue}");
});
```

## List and Tree

### ListView

Virtualized scrollable list for efficient rendering of many items.

```csharp
var listView = new ListView();
listView.style.height = 400;

// Set item source
var items = new List<string>();
for (int i = 0; i < 1000; i++)
{
    items.Add($"Item {i}");
}
listView.itemsSource = items;

// Define how to create items (called when item becomes visible)
listView.makeItem = () =>
{
    var label = new Label();
    label.style.height = 30;
    return label;
};

// Define how to bind data to items
listView.bindItem = (element, index) =>
{
    var label = element as Label;
    label.text = items[index];
};

// Selection
listView.selectionType = SelectionType.Single;
listView.selectedIndex = 0;

listView.onSelectionChange += (selectedItems) =>
{
    foreach (var item in selectedItems)
    {
        Debug.Log($"Selected: {item}");
    }
};

// Reorderable
listView.reorderable = true;
listView.onItemsChosen += (selectedItems) =>
{
    Debug.Log("Items double-clicked or enter pressed");
};
```

**Advanced ListView with custom items:**
```csharp
public class ItemData
{
    public string name;
    public int value;
}

var data = new List<ItemData>
{
    new ItemData { name = "Item A", value = 10 },
    new ItemData { name = "Item B", value = 20 }
};

listView.itemsSource = data;

listView.makeItem = () =>
{
    var container = new VisualElement();
    container.style.flexDirection = FlexDirection.Row;
    container.Add(new Label());
    container.Add(new Label());
    return container;
};

listView.bindItem = (element, index) =>
{
    var labels = element.Query<Label>().ToList();
    labels[0].text = data[index].name;
    labels[1].text = data[index].value.ToString();
};
```

### TreeView

Hierarchical tree control.

```csharp
// TreeView requires more complex setup
// Typically used in Editor for hierarchies
```

## Special Controls

### Scroller

Scrollbar control (usually used internally by ScrollView).

```csharp
var scroller = new Scroller(0, 100, (value) =>
{
    Debug.Log($"Scroll value: {value}");
}, SliderDirection.Vertical);
```

### Image

Displays a texture or sprite.

```csharp
var image = new Image();
image.image = texture2D;
image.sprite = sprite;
image.scaleMode = ScaleMode.ScaleToFit;

// Scale modes:
// ScaleMode.StretchToFill
// ScaleMode.ScaleAndCrop
// ScaleMode.ScaleToFit
```

### IMGUIContainer

Container for legacy IMGUI code.

```csharp
var imguiContainer = new IMGUIContainer(() =>
{
    GUILayout.Label("Legacy IMGUI");
    if (GUILayout.Button("Click"))
    {
        Debug.Log("IMGUI button clicked");
    }
});
```

### TemplateContainer

Result of instantiating a VisualTreeAsset.

```csharp
var visualTree = AssetDatabase.LoadAssetAtPath<VisualTreeAsset>("Assets/UI/Template.uxml");
var instance = visualTree.Instantiate();
// instance is a TemplateContainer
root.Add(instance);
```

## Editor-Only Elements

These require `using UnityEditor.UIElements;`

### ObjectField

Unity object reference picker.

```csharp
var objectField = new ObjectField("Prefab");
objectField.objectType = typeof(GameObject);
objectField.allowSceneObjects = false;
objectField.value = myGameObject;

objectField.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Object: {evt.newValue}");
});
```

### ColorField

Color picker.

```csharp
var colorField = new ColorField("Background");
colorField.value = Color.white;
colorField.showAlpha = true;
colorField.hdr = false;
colorField.showEyeDropper = true;

colorField.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Color: {evt.newValue}");
});
```

### CurveField

Animation curve editor.

```csharp
var curveField = new CurveField("Curve");
curveField.value = AnimationCurve.Linear(0, 0, 1, 1);

curveField.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Curve edited");
});
```

### GradientField

Gradient editor.

```csharp
var gradientField = new GradientField("Gradient");
gradientField.value = new Gradient();

gradientField.RegisterValueChangedCallback(evt =>
{
    Debug.Log("Gradient edited");
});
```

### LayerField, LayerMaskField, TagField

Unity layer and tag pickers.

```csharp
var layerField = new LayerField("Layer");
layerField.value = 0; // Layer index

var maskField = new LayerMaskField("Layer Mask");
maskField.value = -1; // All layers

var tagField = new TagField("Tag");
tagField.value = "Player";
```

### PropertyField

Automatic field for any SerializedProperty.

```csharp
var serializedObject = new SerializedObject(targetObject);
var property = serializedObject.FindProperty("myField");

var propertyField = new PropertyField(property);
propertyField.Bind(serializedObject);

// PropertyField automatically creates appropriate UI based on property type
```

### Toolbar

Toolbar container (Editor).

```csharp
var toolbar = new Toolbar();
toolbar.Add(new ToolbarButton(() => Debug.Log("New")) { text = "New" });
toolbar.Add(new ToolbarButton(() => Debug.Log("Open")) { text = "Open" });
toolbar.Add(new ToolbarSpacer());
toolbar.Add(new ToolbarToggle { text = "Debug" });
```

## Custom Elements

Create custom controls by inheriting from VisualElement:

```csharp
public class CustomControl : VisualElement
{
    private Label titleLabel;
    private Button actionButton;

    // UxmlFactory enables UXML usage
    public new class UxmlFactory : UxmlFactory<CustomControl, UxmlTraits> { }

    public new class UxmlTraits : VisualElement.UxmlTraits
    {
        UxmlStringAttributeDescription titleAttr = new UxmlStringAttributeDescription
        {
            name = "title",
            defaultValue = "Default Title"
        };

        public override void Init(VisualElement ve, IUxmlAttributes bag, CreationContext cc)
        {
            base.Init(ve, bag, cc);
            var control = ve as CustomControl;
            control.Title = titleAttr.GetValueFromBag(bag, cc);
        }
    }

    public string Title
    {
        get => titleLabel.text;
        set => titleLabel.text = value;
    }

    public CustomControl()
    {
        AddToClassList("custom-control");

        titleLabel = new Label();
        titleLabel.AddToClassList("custom-control__title");

        actionButton = new Button(() => OnAction());
        actionButton.text = "Action";
        actionButton.AddToClassList("custom-control__button");

        Add(titleLabel);
        Add(actionButton);
    }

    private void OnAction()
    {
        Debug.Log($"Action triggered for: {Title}");
    }
}
```

**Usage:**
```csharp
var custom = new CustomControl();
custom.Title = "My Control";
root.Add(custom);
```

## Common Patterns

### Confirmation Dialog

```csharp
public class ConfirmDialog : VisualElement
{
    public System.Action OnConfirm;
    public System.Action OnCancel;

    public ConfirmDialog(string message)
    {
        AddToClassList("dialog");
        style.position = Position.Absolute;
        style.left = 0;
        style.right = 0;
        style.top = 0;
        style.bottom = 0;
        style.backgroundColor = new Color(0, 0, 0, 0.5f);

        var panel = new VisualElement();
        panel.AddToClassList("dialog-panel");
        panel.style.backgroundColor = Color.white;
        panel.style.width = 300;
        panel.style.padding = 20;

        panel.Add(new Label(message));

        var buttonRow = new VisualElement();
        buttonRow.style.flexDirection = FlexDirection.Row;
        buttonRow.style.justifyContent = Justify.SpaceAround;

        var confirmBtn = new Button(() =>
        {
            OnConfirm?.Invoke();
            RemoveFromHierarchy();
        });
        confirmBtn.text = "Confirm";

        var cancelBtn = new Button(() =>
        {
            OnCancel?.Invoke();
            RemoveFromHierarchy();
        });
        cancelBtn.text = "Cancel";

        buttonRow.Add(confirmBtn);
        buttonRow.Add(cancelBtn);
        panel.Add(buttonRow);

        Add(panel);
    }
}
```

### Tabbed Interface

```csharp
public class TabbedView : VisualElement
{
    private VisualElement tabBar;
    private VisualElement contentContainer;
    private List<VisualElement> tabs = new List<VisualElement>();
    private int activeTab = 0;

    public TabbedView()
    {
        tabBar = new VisualElement();
        tabBar.style.flexDirection = FlexDirection.Row;
        Add(tabBar);

        contentContainer = new VisualElement();
        contentContainer.style.flexGrow = 1;
        Add(contentContainer);
    }

    public void AddTab(string title, VisualElement content)
    {
        int tabIndex = tabs.Count;

        var tabButton = new Button(() => ShowTab(tabIndex));
        tabButton.text = title;
        tabBar.Add(tabButton);

        content.style.display = tabs.Count == 0 ? DisplayStyle.Flex : DisplayStyle.None;
        tabs.Add(content);
        contentContainer.Add(content);
    }

    private void ShowTab(int index)
    {
        tabs[activeTab].style.display = DisplayStyle.None;
        tabs[index].style.display = DisplayStyle.Flex;
        activeTab = index;
    }
}
```
