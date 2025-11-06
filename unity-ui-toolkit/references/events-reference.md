# Events Reference

Comprehensive guide to UI Toolkit event system, including event types, propagation, and handling patterns.

## Event System Overview

UI Toolkit uses an event propagation system similar to web browsers, with three phases:

1. **Trickle Down** - From root to target (capture phase)
2. **Target** - At the event target element
3. **Bubble Up** - From target back to root (bubble phase)

## Event Registration

### RegisterCallback

Primary method for event handling:

```csharp
element.RegisterCallback<EventType>(CallbackMethod);
element.RegisterCallback<EventType>(CallbackMethod, TrickleDown.TrickleDown);
element.RegisterCallback<EventType>(evt =>
{
    // Inline lambda
}, TrickleDown.NoTrickleDown);
```

**Trickle Down Modes:**
- `TrickleDown.NoTrickleDown` - Bubble phase only (default)
- `TrickleDown.TrickleDown` - Capture/trickle-down phase

### UnregisterCallback

Remove event handlers:

```csharp
element.UnregisterCallback<EventType>(CallbackMethod);
```

**Important:** Lambda expressions cannot be unregistered. Use named methods if you need to unregister.

```csharp
// This CAN be unregistered
void OnClick(ClickEvent evt) { }
element.RegisterCallback<ClickEvent>(OnClick);
element.UnregisterCallback<ClickEvent>(OnClick);

// This CANNOT be unregistered
element.RegisterCallback<ClickEvent>(evt => { });
```

## Mouse Events

### ClickEvent

Fired when left mouse button clicks (down + up on same element).

```csharp
button.RegisterCallback<ClickEvent>(evt =>
{
    Debug.Log($"Clicked at: {evt.position}");
    Debug.Log($"Local position: {evt.localPosition}");
    Debug.Log($"Button: {evt.button}"); // 0 = left, 1 = right, 2 = middle
    Debug.Log($"Click count: {evt.clickCount}"); // 1 = single, 2 = double
    Debug.Log($"Modifiers: Shift={evt.shiftKey}, Ctrl={evt.ctrlKey}, Alt={evt.altKey}");
});
```

**Event Properties:**
- `position` - Mouse position in screen space
- `localPosition` - Mouse position relative to element
- `button` - Mouse button index (0=left, 1=right, 2=middle)
- `clickCount` - Number of clicks (1=single, 2=double, etc.)
- `shiftKey`, `ctrlKey`, `altKey`, `commandKey` - Modifier keys
- `target` - Element that received the event

### MouseDownEvent / MouseUpEvent

Individual mouse button press/release events.

```csharp
element.RegisterCallback<MouseDownEvent>(evt =>
{
    Debug.Log($"Mouse down: button {evt.button}");
    evt.StopPropagation(); // Prevent bubbling
});

element.RegisterCallback<MouseUpEvent>(evt =>
{
    Debug.Log("Mouse up");
});
```

### MouseMoveEvent

Fired when mouse moves over element.

```csharp
element.RegisterCallback<MouseMoveEvent>(evt =>
{
    Debug.Log($"Mouse at: {evt.mousePosition}");
    Debug.Log($"Delta: {evt.mouseDelta}");
});
```

**Properties:**
- `mousePosition` - Current mouse position
- `mouseDelta` - Change since last MouseMoveEvent

### MouseEnterEvent / MouseLeaveEvent

Fired when mouse enters/leaves element bounds (no bubbling).

```csharp
element.RegisterCallback<MouseEnterEvent>(evt =>
{
    element.AddToClassList("hover");
});

element.RegisterCallback<MouseLeaveEvent>(evt =>
{
    element.RemoveFromClassList("hover");
});
```

### MouseOverEvent / MouseOutEvent

Similar to Enter/Leave but DO bubble up through hierarchy.

```csharp
element.RegisterCallback<MouseOverEvent>(evt =>
{
    Debug.Log("Mouse over (bubbles)");
});
```

### WheelEvent

Mouse wheel scroll event.

```csharp
element.RegisterCallback<WheelEvent>(evt =>
{
    Debug.Log($"Wheel delta: {evt.delta}");
    float scrollAmount = evt.delta.y;

    // Prevent default scroll behavior
    evt.StopPropagation();
});
```

## Pointer Events

More modern pointer events that handle mouse, touch, and pen input uniformly.

### PointerDownEvent / PointerUpEvent

```csharp
element.RegisterCallback<PointerDownEvent>(evt =>
{
    Debug.Log($"Pointer {evt.pointerId} down");
    Debug.Log($"Pointer type: {evt.pointerType}"); // mouse, touch, pen
    Debug.Log($"Position: {evt.position}");
    Debug.Log($"Button: {evt.button}");

    // Capture pointer (continue receiving events even if pointer leaves)
    element.CapturePointer(evt.pointerId);
});

element.RegisterCallback<PointerUpEvent>(evt =>
{
    Debug.Log("Pointer up");
    element.ReleasePointer(evt.pointerId);
});
```

**Properties:**
- `pointerId` - Unique pointer identifier
- `pointerType` - "mouse", "touch", "pen"
- `position` - Pointer position
- `localPosition` - Position relative to element
- `button` - Button/touch index
- `pressure` - Pressure (0-1, for pen/touch)

### PointerMoveEvent

```csharp
element.RegisterCallback<PointerMoveEvent>(evt =>
{
    Debug.Log($"Pointer moved to: {evt.position}");
    Debug.Log($"Delta: {evt.deltaPosition}");
});
```

### PointerEnterEvent / PointerLeaveEvent

```csharp
element.RegisterCallback<PointerEnterEvent>(evt =>
{
    element.style.backgroundColor = Color.gray;
});

element.RegisterCallback<PointerLeaveEvent>(evt =>
{
    element.style.backgroundColor = Color.white;
});
```

### PointerCancelEvent

Fired when pointer input is cancelled (e.g., system interrupt).

```csharp
element.RegisterCallback<PointerCancelEvent>(evt =>
{
    Debug.Log("Pointer cancelled");
    element.ReleasePointer(evt.pointerId);
});
```

### PointerCaptureEvent / PointerCaptureOutEvent

Fired when pointer capture is acquired/lost.

```csharp
element.RegisterCallback<PointerCaptureEvent>(evt =>
{
    Debug.Log("Captured pointer");
});

element.RegisterCallback<PointerCaptureOutEvent>(evt =>
{
    Debug.Log("Lost pointer capture");
});
```

## Keyboard Events

### KeyDownEvent / KeyUpEvent

```csharp
element.RegisterCallback<KeyDownEvent>(evt =>
{
    Debug.Log($"Key pressed: {evt.keyCode}");
    Debug.Log($"Character: {evt.character}");
    Debug.Log($"Modifiers: Shift={evt.shiftKey}, Ctrl={evt.ctrlKey}");

    if (evt.keyCode == KeyCode.Return)
    {
        Debug.Log("Enter pressed");
        evt.StopPropagation();
    }

    // Check for key combinations
    if (evt.ctrlKey && evt.keyCode == KeyCode.S)
    {
        Debug.Log("Ctrl+S pressed");
        evt.PreventDefault();
    }
});
```

**Properties:**
- `keyCode` - Unity KeyCode enum value
- `character` - Character representation (for text input)
- `shiftKey`, `ctrlKey`, `altKey`, `commandKey` - Modifier keys
- `actionKey` - Ctrl (Windows/Linux) or Cmd (macOS)

**Common Patterns:**
```csharp
// Escape key to close
if (evt.keyCode == KeyCode.Escape)
{
    CloseDialog();
}

// Ctrl/Cmd + specific key
if (evt.actionKey && evt.keyCode == KeyCode.N)
{
    CreateNew();
}

// Arrow key navigation
switch (evt.keyCode)
{
    case KeyCode.UpArrow:
        NavigateUp();
        break;
    case KeyCode.DownArrow:
        NavigateDown();
        break;
}
```

## Focus Events

### FocusInEvent / FocusOutEvent

```csharp
textField.RegisterCallback<FocusInEvent>(evt =>
{
    Debug.Log("Gained focus");
    textField.AddToClassList("focused");
});

textField.RegisterCallback<FocusOutEvent>(evt =>
{
    Debug.Log("Lost focus");
    textField.RemoveFromClassList("focused");
});
```

### BlurEvent / FocusEvent

Alternative focus events.

```csharp
element.RegisterCallback<FocusEvent>(evt =>
{
    Debug.Log("Focused");
});

element.RegisterCallback<BlurEvent>(evt =>
{
    Debug.Log("Blurred");
});
```

**Programmatic Focus:**
```csharp
element.focusable = true;
element.Focus();
element.Blur();
```

## Change Events

### ChangeEvent\<T>

Generic event for value changes (typed to field's value type).

```csharp
// TextField
textField.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Text changed: '{evt.previousValue}' -> '{evt.newValue}'");
});

// Slider
slider.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Value: {evt.previousValue} -> {evt.newValue}");
});

// Toggle
toggle.RegisterValueChangedCallback(evt =>
{
    Debug.Log($"Toggled: {evt.newValue}");
});

// Or use RegisterCallback with ChangeEvent<T>
slider.RegisterCallback<ChangeEvent<float>>(evt =>
{
    Debug.Log($"Slider value: {evt.newValue}");
});
```

**Properties:**
- `previousValue` - Value before change
- `newValue` - Value after change
- `target` - Element that changed

### InputEvent

Fired during text input (before ChangeEvent).

```csharp
textField.RegisterCallback<InputEvent>(evt =>
{
    Debug.Log($"Input: {evt.newData}");
    Debug.Log($"Previous: {evt.previousData}");
});
```

## Navigation Events

### NavigationMoveEvent

Fired on arrow key navigation.

```csharp
element.RegisterCallback<NavigationMoveEvent>(evt =>
{
    Debug.Log($"Navigate: {evt.direction}");
    // direction: NavigationMoveEvent.Direction (Left, Up, Right, Down)

    switch (evt.direction)
    {
        case NavigationMoveEvent.Direction.Left:
            SelectPrevious();
            break;
        case NavigationMoveEvent.Direction.Right:
            SelectNext();
            break;
    }

    evt.PreventDefault();
});
```

### NavigationSubmitEvent

Fired on Enter/Return key.

```csharp
element.RegisterCallback<NavigationSubmitEvent>(evt =>
{
    Debug.Log("Submit");
    SubmitForm();
    evt.StopPropagation();
});
```

### NavigationCancelEvent

Fired on Escape key.

```csharp
element.RegisterCallback<NavigationCancelEvent>(evt =>
{
    Debug.Log("Cancel");
    CloseDialog();
});
```

## Drag and Drop Events

### DragEnterEvent / DragLeaveEvent

```csharp
element.RegisterCallback<DragEnterEvent>(evt =>
{
    Debug.Log("Drag entered");
    element.AddToClassList("drag-over");
});

element.RegisterCallback<DragLeaveEvent>(evt =>
{
    Debug.Log("Drag left");
    element.RemoveFromClassList("drag-over");
});
```

### DragUpdatedEvent

Continuously fired while dragging over element.

```csharp
element.RegisterCallback<DragUpdatedEvent>(evt =>
{
    Debug.Log($"Drag position: {evt.mousePosition}");

    // Accept drag
    DragAndDrop.visualMode = DragAndDropVisualMode.Copy;
});
```

### DragPerformEvent

Fired when drag is released over element.

```csharp
element.RegisterCallback<DragPerformEvent>(evt =>
{
    Debug.Log("Drop performed");

    // Access dragged objects
    foreach (var obj in DragAndDrop.objectReferences)
    {
        Debug.Log($"Dropped: {obj.name}");
    }

    DragAndDrop.AcceptDrag();
});
```

### DragExitedEvent

Fired when drag operation ends.

```csharp
element.RegisterCallback<DragExitedEvent>(evt =>
{
    Debug.Log("Drag exited");
    element.RemoveFromClassList("drag-over");
});
```

## Geometry Events

### GeometryChangedEvent

Fired when element's layout (size/position) changes.

```csharp
element.RegisterCallback<GeometryChangedEvent>(evt =>
{
    Debug.Log($"Old: {evt.oldRect}");
    Debug.Log($"New: {evt.newRect}");
    Debug.Log($"Size: {evt.newRect.size}");

    // Respond to size changes
    if (evt.newRect.width > 500)
    {
        element.AddToClassList("wide");
    }
});
```

### AttachToPanelEvent / DetachFromPanelEvent

Fired when element is added/removed from visual tree.

```csharp
element.RegisterCallback<AttachToPanelEvent>(evt =>
{
    Debug.Log("Attached to panel");
    InitializeElement();
});

element.RegisterCallback<DetachFromPanelEvent>(evt =>
{
    Debug.Log("Detached from panel");
    Cleanup();
});
```

## Custom Events

### Creating Custom Events

```csharp
public class CustomEvent : EventBase<CustomEvent>
{
    public string data;

    public static CustomEvent GetPooled(string data)
    {
        var evt = GetPooled();
        evt.data = data;
        return evt;
    }
}

// Dispatch custom event
using (var evt = CustomEvent.GetPooled("my data"))
{
    evt.target = element;
    element.SendEvent(evt);
}

// Register for custom event
element.RegisterCallback<CustomEvent>(evt =>
{
    Debug.Log($"Custom event: {evt.data}");
});
```

## Event Control Methods

### StopPropagation

Stops event from propagating to other handlers.

```csharp
element.RegisterCallback<ClickEvent>(evt =>
{
    Debug.Log("Handling click");
    evt.StopPropagation(); // Won't bubble to parent
});
```

### StopImmediatePropagation

Stops event from reaching other handlers on same element.

```csharp
element.RegisterCallback<ClickEvent>(evt =>
{
    evt.StopImmediatePropagation(); // Other handlers on this element won't run
});
```

### PreventDefault

Prevents default behavior of event.

```csharp
element.RegisterCallback<KeyDownEvent>(evt =>
{
    if (evt.keyCode == KeyCode.Tab)
    {
        evt.PreventDefault(); // Prevent default tab navigation
        CustomTabHandler();
    }
});
```

### Capturing and Releasing

Capture all pointer events to an element:

```csharp
element.RegisterCallback<PointerDownEvent>(evt =>
{
    element.CapturePointer(evt.pointerId);
});

element.RegisterCallback<PointerUpEvent>(evt =>
{
    element.ReleasePointer(evt.pointerId);
});

// Check if captured
if (element.HasPointerCapture(pointerId))
{
    // Element has capture
}
```

## Event Propagation Phases

### Phase Order

1. **TrickleDown (Capture)** - Root → Target
2. **AtTarget** - At target element
3. **BubbleUp** - Target → Root

```csharp
// Register in trickle-down phase
parent.RegisterCallback<ClickEvent>(evt =>
{
    Debug.Log("Parent trickle down (runs first)");
}, TrickleDown.TrickleDown);

// Register in bubble-up phase (default)
parent.RegisterCallback<ClickEvent>(evt =>
{
    Debug.Log("Parent bubble up (runs last)");
});

// Target element
child.RegisterCallback<ClickEvent>(evt =>
{
    Debug.Log("Child clicked (runs middle)");
});

// Output when child is clicked:
// "Parent trickle down (runs first)"
// "Child clicked (runs middle)"
// "Parent bubble up (runs last)"
```

### Practical Example

```csharp
// Stop event in capture phase to intercept before target
container.RegisterCallback<ClickEvent>(evt =>
{
    if (someCondition)
    {
        Debug.Log("Intercepted in capture phase");
        evt.StopPropagation();
        // Child won't receive event
    }
}, TrickleDown.TrickleDown);

// This might not run if intercepted above
button.RegisterCallback<ClickEvent>(evt =>
{
    Debug.Log("Button clicked");
});
```

## Common Patterns

### Debouncing Input

```csharp
private IEnumerator debounceCoroutine;
private float debounceTime = 0.5f;

textField.RegisterValueChangedCallback(evt =>
{
    if (debounceCoroutine != null)
    {
        StopCoroutine(debounceCoroutine);
    }

    debounceCoroutine = StartCoroutine(DebounceSearch(evt.newValue));
});

IEnumerator DebounceSearch(string query)
{
    yield return new WaitForSeconds(debounceTime);
    PerformSearch(query);
}
```

### Click Outside to Close

```csharp
public class Modal : VisualElement
{
    private VisualElement backdrop;
    private VisualElement panel;

    public Modal()
    {
        backdrop = new VisualElement();
        backdrop.style.position = Position.Absolute;
        backdrop.style.left = 0;
        backdrop.style.right = 0;
        backdrop.style.top = 0;
        backdrop.style.bottom = 0;

        backdrop.RegisterCallback<ClickEvent>(evt =>
        {
            Close();
        });

        panel = new VisualElement();
        panel.RegisterCallback<ClickEvent>(evt =>
        {
            evt.StopPropagation(); // Prevent backdrop click
        });

        backdrop.Add(panel);
        Add(backdrop);
    }

    private void Close()
    {
        RemoveFromHierarchy();
    }
}
```

### Drag Reordering

```csharp
private Vector2 dragStart;
private bool isDragging;

element.RegisterCallback<PointerDownEvent>(evt =>
{
    dragStart = evt.position;
    isDragging = true;
    element.CapturePointer(evt.pointerId);
});

element.RegisterCallback<PointerMoveEvent>(evt =>
{
    if (isDragging)
    {
        Vector2 delta = evt.position - dragStart;
        element.style.left = delta.x;
        element.style.top = delta.y;
    }
});

element.RegisterCallback<PointerUpEvent>(evt =>
{
    isDragging = false;
    element.ReleasePointer(evt.pointerId);
});
```

### Form Validation on Submit

```csharp
form.RegisterCallback<NavigationSubmitEvent>(evt =>
{
    if (ValidateForm())
    {
        SubmitForm();
    }
    else
    {
        ShowErrors();
        evt.PreventDefault();
    }
});

bool ValidateForm()
{
    var nameField = form.Q<TextField>("name");
    var emailField = form.Q<TextField>("email");

    bool isValid = true;

    if (string.IsNullOrEmpty(nameField.value))
    {
        nameField.AddToClassList("error");
        isValid = false;
    }

    if (!IsValidEmail(emailField.value))
    {
        emailField.AddToClassList("error");
        isValid = false;
    }

    return isValid;
}
```

### Keyboard Shortcuts

```csharp
root.RegisterCallback<KeyDownEvent>(evt =>
{
    // Ctrl/Cmd + S to save
    if (evt.actionKey && evt.keyCode == KeyCode.S)
    {
        Save();
        evt.PreventDefault();
    }

    // Ctrl/Cmd + Z to undo
    if (evt.actionKey && evt.keyCode == KeyCode.Z)
    {
        if (evt.shiftKey)
            Redo();
        else
            Undo();
        evt.PreventDefault();
    }

    // Delete key
    if (evt.keyCode == KeyCode.Delete)
    {
        DeleteSelected();
    }
}, TrickleDown.TrickleDown); // Capture to intercept before focused elements
```

## Performance Considerations

### Event Pooling

Events are pooled for performance. Don't store event references:

```csharp
// BAD - event will be recycled
ClickEvent storedEvent;
element.RegisterCallback<ClickEvent>(evt =>
{
    storedEvent = evt; // Don't do this
});

// GOOD - extract needed data
Vector2 clickPosition;
element.RegisterCallback<ClickEvent>(evt =>
{
    clickPosition = evt.position; // Store data, not event
});
```

### Unregister When Done

Prevent memory leaks by unregistering callbacks:

```csharp
void OnEnable()
{
    button.RegisterCallback<ClickEvent>(OnClick);
}

void OnDisable()
{
    button.UnregisterCallback<ClickEvent>(OnClick);
}

void OnClick(ClickEvent evt)
{
    Debug.Log("Clicked");
}
```

### Avoid Heavy Processing in Event Handlers

```csharp
// BAD - heavy work in event handler
textField.RegisterCallback<InputEvent>(evt =>
{
    PerformExpensiveSearch(evt.newData); // Every keystroke
});

// GOOD - debounce or defer
textField.RegisterCallback<InputEvent>(evt =>
{
    ScheduleDelayedSearch(evt.newData);
});
```

## Debugging Events

### Log Event Flow

```csharp
void LogEvent<T>(T evt, string phase) where T : EventBase
{
    Debug.Log($"[{phase}] {evt.GetType().Name} on {(evt.target as VisualElement)?.name}");
}

parent.RegisterCallback<ClickEvent>(evt => LogEvent(evt, "Parent Capture"), TrickleDown.TrickleDown);
child.RegisterCallback<ClickEvent>(evt => LogEvent(evt, "Child Target"));
parent.RegisterCallback<ClickEvent>(evt => LogEvent(evt, "Parent Bubble"));
```

### UI Toolkit Debugger

Use Window > UI Toolkit > Debugger to:
- View event propagation in real-time
- Inspect which handlers are registered
- See event properties
- Monitor event performance
