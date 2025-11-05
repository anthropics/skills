# UI Toolkit Best Practices

Comprehensive guide to performance optimization, architecture patterns, and common pitfalls in Unity UI Toolkit.

## Performance Optimization

### 1. Use USS Files Instead of Inline Styles

**Why:** Inline styles consume more memory per element and reduce style reusability.

```csharp
// BAD - Inline styles
for (int i = 0; i < 1000; i++)
{
    var element = new VisualElement();
    element.style.width = 100;
    element.style.height = 100;
    element.style.backgroundColor = Color.blue;
}

// GOOD - USS classes
for (int i = 0; i < 1000; i++)
{
    var element = new VisualElement();
    element.AddToClassList("item");
}
```

**USS:**
```css
.item {
    width: 100px;
    height: 100px;
    background-color: rgb(0, 0, 255);
}
```

### 2. Minimize Layout Recalculations

**Why:** Changing layout properties triggers expensive layout recalculations.

```csharp
// BAD - Multiple layout changes
element.style.width = 100;
element.style.height = 100;
element.style.marginLeft = 10;
element.style.marginTop = 10;
// Triggers 4 layout recalculations

// BETTER - Batch changes (still triggers recalc, but organized)
element.style.width = 100;
element.style.height = 100;
element.style.marginLeft = 10;
element.style.marginTop = 10;

// BEST - Use USS classes
element.AddToClassList("sized-item");
// Triggers 1 layout recalculation
```

**Avoid animating layout properties:**
```csharp
// BAD - Animates width (triggers layout every frame)
void Update()
{
    element.style.width = Mathf.Lerp(100, 200, t);
}

// GOOD - Use transform (no layout recalculation)
void Update()
{
    element.style.scale = new Scale(new Vector2(Mathf.Lerp(1, 2, t), 1));
}
```

### 3. Use ListView for Long Lists

**Why:** ListView virtualizes items, rendering only visible ones.

```csharp
// BAD - Creates 1000 elements (all in memory)
var container = new ScrollView();
for (int i = 0; i < 1000; i++)
{
    container.Add(new Label($"Item {i}"));
}

// GOOD - ListView virtualizes (only renders visible items)
var listView = new ListView();
listView.itemsSource = Enumerable.Range(0, 1000).ToList();
listView.makeItem = () => new Label();
listView.bindItem = (element, index) =>
{
    (element as Label).text = $"Item {index}";
};
```

### 4. Pool and Reuse Elements

**Why:** Creating/destroying elements is expensive.

```csharp
// Example: Object pooling for dynamic UI
public class ElementPool<T> where T : VisualElement, new()
{
    private Stack<T> pool = new Stack<T>();
    private VisualElement container;

    public ElementPool(VisualElement container)
    {
        this.container = container;
    }

    public T Get()
    {
        if (pool.Count > 0)
        {
            var element = pool.Pop();
            element.style.display = DisplayStyle.Flex;
            return element;
        }
        return new T();
    }

    public void Release(T element)
    {
        element.style.display = DisplayStyle.None;
        pool.Push(element);
    }
}
```

### 5. Use display: none Instead of Removing Elements

**Why:** Removing and re-adding elements is more expensive than hiding.

```csharp
// BAD - Remove and re-add
if (shouldHide)
{
    element.RemoveFromHierarchy();
}
else
{
    parent.Add(element);
}

// GOOD - Toggle display
element.style.display = shouldHide ? DisplayStyle.None : DisplayStyle.Flex;

// ALSO GOOD - Toggle visibility (still takes layout space)
element.visible = !shouldHide;
```

### 6. Avoid Deep Element Nesting

**Why:** Deep hierarchies slow down layout calculations and event propagation.

```csharp
// BAD - 6 levels deep
container
  └─ wrapper
      └─ inner-wrapper
          └─ content-wrapper
              └─ item-container
                  └─ item

// GOOD - Flatter hierarchy (2-3 levels)
container
  └─ item
```

### 7. Debounce Frequent Updates

**Why:** Prevents excessive updates from rapid events.

```csharp
private Coroutine updateCoroutine;

textField.RegisterValueChangedCallback(evt =>
{
    if (updateCoroutine != null)
        StopCoroutine(updateCoroutine);

    updateCoroutine = StartCoroutine(DelayedUpdate(evt.newValue));
});

IEnumerator DelayedUpdate(string value)
{
    yield return new WaitForSeconds(0.3f);
    PerformExpensiveOperation(value);
}
```

### 8. Optimize Event Handlers

**Why:** Event handlers run frequently; keep them lightweight.

```csharp
// BAD - Heavy work in event handler
element.RegisterCallback<MouseMoveEvent>(evt =>
{
    PerformExpensiveRaycast();
    UpdateComplexUI();
    RecalculateAllData();
});

// GOOD - Lightweight handler, defer heavy work
element.RegisterCallback<MouseMoveEvent>(evt =>
{
    mousePosition = evt.position;
    isDirty = true; // Process in Update or coroutine
});

void Update()
{
    if (isDirty)
    {
        isDirty = false;
        PerformExpensiveWork();
    }
}
```

### 9. Unregister Event Callbacks

**Why:** Prevents memory leaks from lingering event handlers.

```csharp
public class UIController : MonoBehaviour
{
    private Button button;

    void OnEnable()
    {
        button = root.Q<Button>("my-button");
        button.RegisterCallback<ClickEvent>(OnClick);
    }

    void OnDisable()
    {
        button?.UnregisterCallback<ClickEvent>(OnClick);
    }

    void OnClick(ClickEvent evt) { }
}
```

### 10. Use Efficient Selectors

**Why:** Complex selectors are slower to match.

```css
/* SLOW - Complex descendant selector */
.container .wrapper .item .label {
    color: white;
}

/* FAST - Simple class selector */
.item-label {
    color: white;
}
```

## Architecture Patterns

### 1. Separation of Concerns

Keep UXML (structure), USS (style), and C# (logic) separate.

**Project Structure:**
```
Assets/
├── UI/
│   ├── Views/
│   │   ├── MainMenu.uxml
│   │   ├── GameHUD.uxml
│   │   └── SettingsPanel.uxml
│   ├── Styles/
│   │   ├── Common.uss
│   │   ├── Buttons.uss
│   │   └── Themes.uss
│   └── Scripts/
│       ├── MainMenuController.cs
│       ├── GameHUDController.cs
│       └── SettingsPanelController.cs
```

### 2. MVC/MVP Pattern

**Model:**
```csharp
public class PlayerData
{
    public string Name { get; set; }
    public int Score { get; set; }
    public int Health { get; set; }
}
```

**View:**
```csharp
public class PlayerView
{
    private Label nameLabel;
    private Label scoreLabel;
    private ProgressBar healthBar;

    public PlayerView(VisualElement root)
    {
        nameLabel = root.Q<Label>("player-name");
        scoreLabel = root.Q<Label>("player-score");
        healthBar = root.Q<ProgressBar>("health-bar");
    }

    public void UpdateName(string name)
    {
        nameLabel.text = name;
    }

    public void UpdateScore(int score)
    {
        scoreLabel.text = $"Score: {score}";
    }

    public void UpdateHealth(int health, int maxHealth)
    {
        healthBar.value = health;
        healthBar.highValue = maxHealth;
    }
}
```

**Controller/Presenter:**
```csharp
public class PlayerController
{
    private PlayerData model;
    private PlayerView view;

    public PlayerController(PlayerData model, PlayerView view)
    {
        this.model = model;
        this.view = view;
        UpdateView();
    }

    public void SetScore(int score)
    {
        model.Score = score;
        view.UpdateScore(score);
    }

    public void TakeDamage(int damage)
    {
        model.Health -= damage;
        view.UpdateHealth(model.Health, 100);
    }

    private void UpdateView()
    {
        view.UpdateName(model.Name);
        view.UpdateScore(model.Score);
        view.UpdateHealth(model.Health, 100);
    }
}
```

### 3. Component-Based UI

Create reusable UI components:

```csharp
public class Card : VisualElement
{
    public new class UxmlFactory : UxmlFactory<Card, UxmlTraits> { }

    private Label titleLabel;
    private Label descriptionLabel;
    private Button actionButton;

    public string Title
    {
        get => titleLabel.text;
        set => titleLabel.text = value;
    }

    public string Description
    {
        get => descriptionLabel.text;
        set => descriptionLabel.text = value;
    }

    public event System.Action OnAction;

    public Card()
    {
        AddToClassList("card");

        titleLabel = new Label();
        titleLabel.AddToClassList("card__title");

        descriptionLabel = new Label();
        descriptionLabel.AddToClassList("card__description");

        actionButton = new Button(() => OnAction?.Invoke());
        actionButton.text = "Action";
        actionButton.AddToClassList("card__button");

        Add(titleLabel);
        Add(descriptionLabel);
        Add(actionButton);
    }
}

// Usage
var card = new Card();
card.Title = "Card Title";
card.Description = "Card description text";
card.OnAction += () => Debug.Log("Card action!");
root.Add(card);
```

### 4. Service Locator for UI Management

```csharp
public class UIManager : MonoBehaviour
{
    private static UIManager instance;
    public static UIManager Instance => instance;

    private Dictionary<string, VisualElement> panels = new Dictionary<string, VisualElement>();
    private UIDocument document;

    void Awake()
    {
        instance = this;
        document = GetComponent<UIDocument>();
    }

    public void RegisterPanel(string name, VisualElement panel)
    {
        panels[name] = panel;
        panel.style.display = DisplayStyle.None;
    }

    public void ShowPanel(string name)
    {
        if (panels.TryGetValue(name, out var panel))
        {
            foreach (var p in panels.Values)
                p.style.display = DisplayStyle.None;

            panel.style.display = DisplayStyle.Flex;
        }
    }

    public T GetPanel<T>(string name) where T : VisualElement
    {
        return panels.TryGetValue(name, out var panel) ? panel as T : null;
    }
}

// Usage
UIManager.Instance.ShowPanel("MainMenu");
```

### 5. Event-Driven Communication

Use events to decouple UI from game logic:

```csharp
// Events
public class GameEvents
{
    public static event System.Action<int> OnScoreChanged;
    public static event System.Action<int, int> OnHealthChanged;
    public static event System.Action<string> OnMessageReceived;

    public static void ScoreChanged(int newScore) => OnScoreChanged?.Invoke(newScore);
    public static void HealthChanged(int current, int max) => OnHealthChanged?.Invoke(current, max);
    public static void MessageReceived(string message) => OnMessageReceived?.Invoke(message);
}

// UI listens to events
public class HUDController : MonoBehaviour
{
    private Label scoreLabel;
    private ProgressBar healthBar;
    private Label messageLabel;

    void OnEnable()
    {
        var root = GetComponent<UIDocument>().rootVisualElement;
        scoreLabel = root.Q<Label>("score");
        healthBar = root.Q<ProgressBar>("health");
        messageLabel = root.Q<Label>("message");

        GameEvents.OnScoreChanged += UpdateScore;
        GameEvents.OnHealthChanged += UpdateHealth;
        GameEvents.OnMessageReceived += ShowMessage;
    }

    void OnDisable()
    {
        GameEvents.OnScoreChanged -= UpdateScore;
        GameEvents.OnHealthChanged -= UpdateHealth;
        GameEvents.OnMessageReceived -= ShowMessage;
    }

    void UpdateScore(int score)
    {
        scoreLabel.text = $"Score: {score}";
    }

    void UpdateHealth(int current, int max)
    {
        healthBar.value = current;
        healthBar.highValue = max;
    }

    void ShowMessage(string message)
    {
        messageLabel.text = message;
    }
}

// Game logic triggers events
public class Player : MonoBehaviour
{
    private int score;

    public void AddScore(int points)
    {
        score += points;
        GameEvents.ScoreChanged(score);
    }
}
```

## Styling Best Practices

### 1. Use BEM Naming Convention

**Block Element Modifier** provides clear, maintainable class names:

```css
/* Block */
.card { }

/* Elements */
.card__title { }
.card__content { }
.card__button { }

/* Modifiers */
.card--highlighted { }
.card--large { }
.card__button--primary { }
.card__button--disabled { }
```

### 2. Create a Design System

Define reusable variables and utilities:

```css
/* variables.uss */
:root {
    /* Colors */
    --color-primary: rgb(0, 120, 215);
    --color-secondary: rgb(100, 100, 100);
    --color-success: rgb(0, 200, 0);
    --color-error: rgb(200, 0, 0);
    --color-warning: rgb(255, 165, 0);

    --color-bg-primary: rgb(255, 255, 255);
    --color-bg-secondary: rgb(240, 240, 240);
    --color-text-primary: rgb(0, 0, 0);
    --color-text-secondary: rgb(100, 100, 100);

    /* Spacing */
    --spacing-xs: 4px;
    --spacing-sm: 8px;
    --spacing-md: 16px;
    --spacing-lg: 24px;
    --spacing-xl: 32px;

    /* Typography */
    --font-size-sm: 12px;
    --font-size-md: 14px;
    --font-size-lg: 16px;
    --font-size-xl: 20px;

    /* Layout */
    --border-radius: 4px;
    --border-width: 1px;
    --transition-speed: 0.3s;
}

/* utilities.uss */
.text-center {
    -unity-text-align: middle-center;
}

.m-0 { margin: 0; }
.m-sm { margin: var(--spacing-sm); }
.m-md { margin: var(--spacing-md); }
.m-lg { margin: var(--spacing-lg); }

.p-0 { padding: 0; }
.p-sm { padding: var(--spacing-sm); }
.p-md { padding: var(--spacing-md); }
.p-lg { padding: var(--spacing-lg); }

.flex-row {
    flex-direction: row;
}

.flex-column {
    flex-direction: column;
}

.flex-center {
    justify-content: center;
    align-items: center;
}

.flex-1 {
    flex-grow: 1;
}

.hide {
    display: none;
}

.show {
    display: flex;
}
```

### 3. Organize Stylesheets by Concern

```
Styles/
├── base.uss           # Reset, base element styles
├── variables.uss      # CSS variables
├── utilities.uss      # Utility classes
├── components/
│   ├── buttons.uss
│   ├── cards.uss
│   ├── forms.uss
│   └── modals.uss
└── layouts/
    ├── header.uss
    ├── sidebar.uss
    └── grid.uss
```

### 4. Responsive Design Patterns

Since media queries aren't supported, use C# for responsiveness:

```csharp
root.RegisterCallback<GeometryChangedEvent>(evt =>
{
    float width = evt.newRect.width;

    if (width < 600)
    {
        root.AddToClassList("layout-mobile");
        root.RemoveFromClassList("layout-desktop");
    }
    else
    {
        root.AddToClassList("layout-desktop");
        root.RemoveFromClassList("layout-mobile");
    }
});
```

```css
/* Mobile layout */
.layout-mobile .sidebar {
    width: 100%;
    flex-direction: column;
}

/* Desktop layout */
.layout-desktop .sidebar {
    width: 250px;
    flex-direction: row;
}
```

## Common Pitfalls

### 1. Forgetting to Set Panel Settings

**Problem:** UI doesn't render in scene.

**Solution:**
```csharp
// Create PanelSettings asset: Create > UI Toolkit > Panel Settings
// Assign to UIDocument component in Inspector
```

### 2. Elements Not Appearing

**Common causes and solutions:**

```csharp
// 1. Parent has no size
container.style.width = 0; // Elements inside won't show
// Fix: Give container a size
container.style.width = 200;
container.style.height = 200;

// 2. Element is outside parent bounds with overflow:hidden
parent.style.overflow = Overflow.Hidden;
child.style.position = Position.Absolute;
child.style.left = 1000; // Outside parent
// Fix: Adjust position or change overflow

// 3. Display is set to none
element.style.display = DisplayStyle.None;
// Fix: Set to Flex
element.style.display = DisplayStyle.Flex;

// 4. Visibility is hidden
element.visible = false;
// Fix: Set visible
element.visible = true;

// 5. Opacity is 0
element.style.opacity = 0;
// Fix: Set opacity
element.style.opacity = 1;

// 6. Z-index issue (in AbsolutePosition)
element1.style.position = Position.Absolute;
element1.style.zIndex = 1; // Behind
element2.style.zIndex = 10; // In front
```

### 3. Layout Not Working as Expected

```csharp
// Problem: Items not centering
container.style.justifyContent = Justify.Center; // Doesn't work on Column

// Solution: Check flex-direction
container.style.flexDirection = FlexDirection.Row;
container.style.justifyContent = Justify.Center; // Now works

// For vertical centering in Column:
container.style.flexDirection = FlexDirection.Column;
container.style.alignItems = Align.Center; // Horizontal centering in Column
container.style.justifyContent = Justify.Center; // Vertical centering in Column
```

### 4. Styles Not Applying

```csharp
// 1. USS file not loaded
var root = GetComponent<UIDocument>().rootVisualElement;
// Fix: Load USS
var styleSheet = AssetDatabase.LoadAssetAtPath<StyleSheet>("Assets/UI/Styles.uss");
root.styleSheets.Add(styleSheet);

// 2. Selector specificity too low
// CSS: .button { color: blue; }
// Inline style overrides it
element.style.color = Color.red; // This wins
// Fix: Avoid inline styles or use !important (not recommended)

// 3. Typo in class name
element.AddToClassList("primery-button"); // Typo
// Fix: Check spelling

// 4. Element created after stylesheet loaded
styleSheet.Add(...);
element = new Button(); // Styles apply
root.Add(element);
```

### 5. Memory Leaks from Event Handlers

```csharp
// Problem: Lambda captures create leaks
void CreateButton()
{
    var button = new Button();
    var data = new HeavyData(); // Captured by lambda
    button.clicked += () =>
    {
        Debug.Log(data.value); // Keeps data alive
    };
}

// Solution: Use named methods and unregister
void OnEnable()
{
    button.clicked += OnButtonClick;
}

void OnDisable()
{
    button.clicked -= OnButtonClick;
}

void OnButtonClick()
{
    // No capture
}
```

### 6. Accessing Elements Before They Exist

```csharp
// Problem: Query before UXML loaded
void Awake()
{
    var button = GetComponent<UIDocument>().rootVisualElement.Q<Button>("btn");
    // button is null - UXML not loaded yet
}

// Solution: Wait for GeometryChangedEvent or use OnEnable
void OnEnable()
{
    var root = GetComponent<UIDocument>().rootVisualElement;
    root.schedule.Execute(() =>
    {
        var button = root.Q<Button>("btn"); // Now exists
    }).ExecuteLater(0);
}
```

### 7. Binding Without Calling Bind()

```csharp
// Problem: Binding path set but not bound
textField.bindingPath = "playerName"; // Not enough

// Solution: Call Bind()
var serializedObject = new SerializedObject(target);
textField.bindingPath = "playerName";
textField.Bind(serializedObject); // Now bound
```

### 8. Modifying Collections During Iteration

```csharp
// Problem: Modifying children while iterating
foreach (var child in container.Children())
{
    container.Remove(child); // Throws exception
}

// Solution: Use ToList() to create copy
foreach (var child in container.Children().ToList())
{
    container.Remove(child); // Safe
}

// Or use Clear()
container.Clear();
```

## Testing and Debugging

### UI Toolkit Debugger

Access: Window > UI Toolkit > Debugger

**Features:**
- Inspect element hierarchy
- View computed styles
- See event propagation
- Monitor performance
- Edit styles in real-time

### Debug Utilities

```csharp
public static class UIDebug
{
    public static void LogHierarchy(VisualElement element, int depth = 0)
    {
        string indent = new string(' ', depth * 2);
        Debug.Log($"{indent}{element.GetType().Name} - {element.name} ({element.childCount} children)");

        foreach (var child in element.Children())
        {
            LogHierarchy(child, depth + 1);
        }
    }

    public static void LogStyles(VisualElement element)
    {
        Debug.Log($"Element: {element.name}");
        Debug.Log($"  Width: {element.resolvedStyle.width}");
        Debug.Log($"  Height: {element.resolvedStyle.height}");
        Debug.Log($"  Display: {element.resolvedStyle.display}");
        Debug.Log($"  Visibility: {element.resolvedStyle.visibility}");
        Debug.Log($"  Position: {element.layout}");
    }
}

// Usage
UIDebug.LogHierarchy(root);
UIDebug.LogStyles(element);
```

## Migration from UGUI

### Key Differences

| Aspect | UGUI | UI Toolkit |
|--------|------|------------|
| Layout | RectTransform, Anchors | Flexbox |
| Styling | Component properties | USS files |
| Structure | GameObjects | VisualElements |
| Performance | GameObject overhead | Lighter weight |
| Events | UnityEvents, IPointerHandler | Event callbacks |
| Rendering | Canvas | PanelRenderer |

### Migration Strategy

1. **Start with new UI first** - Learn UI Toolkit on new features
2. **Migrate static screens** - Start with menus, settings
3. **Keep dynamic/3D UI in UGUI** - World-space UI may be better in UGUI
4. **Coexist** - Both systems can run simultaneously
5. **Refactor gradually** - No need to migrate everything at once
