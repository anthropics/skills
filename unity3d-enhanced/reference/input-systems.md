# Unity Input Systems

## Overview

Unity has two input systems that cannot be mixed without proper configuration. Understanding which system your project uses and how to configure it correctly is essential to avoid runtime errors.

## The Two Systems

### Legacy Input Manager (Old)

**Package**: Built into Unity core
**Namespace**: `UnityEngine.Input`
**Available**: All Unity versions

```csharp
using UnityEngine;

// Simple, straightforward API
Vector3 mousePos = Input.mousePosition;
bool spacePressed = Input.GetKeyDown(KeyCode.Space);
float horizontal = Input.GetAxis("Horizontal");
bool leftClick = Input.GetMouseButtonDown(0);
```

**Pros**:
- Simple and straightforward
- Built into Unity core
- No additional setup required
- Good for simple projects and prototypes

**Cons**:
- Limited rebinding capabilities
- Hard-coded input strings
- No multi-device management
- Deprecated (will be removed eventually)

### New Input System (2019.1+)

**Package**: `com.unity.inputsystem`
**Namespace**: `UnityEngine.InputSystem`
**Available**: Unity 2019.1+

```csharp
using UnityEngine;
using UnityEngine.InputSystem;

private Keyboard keyboard;
private Mouse mouse;

void Awake()
{
    keyboard = Keyboard.current;
    mouse = Mouse.current;
}

void Update()
{
    // Always null-check devices
    if (keyboard == null)
    {
        keyboard = Keyboard.current;
        if (keyboard == null) return;
    }

    if (keyboard.spaceKey.wasPressedThisFrame)
    {
        Jump();
    }

    if (mouse != null && mouse.leftButton.wasPressedThisFrame)
    {
        Shoot();
    }
}
```

**Pros**:
- Flexible and powerful
- Full rebinding support
- Asset-based input configuration
- Better multi-device support (gamepad, touch, VR)
- Action-based workflow
- Event-driven architecture

**Cons**:
- More complex setup
- Requires package installation
- Steeper learning curve
- Null-checking required for devices

## Configuration

### Location
`ProjectSettings/ProjectSettings.asset` (line ~681)

```yaml
activeInputHandler: [value]
```

### Values

| Value | Name | Legacy API | New API | Use Case |
|-------|------|------------|---------|----------|
| 0 | Input Manager (Old) | ✓ | ✗ | Legacy projects only |
| 1 | Input System (New) | ✗ | ✓ | New projects with new system |
| 2 | Both | ✓ | ✓ | **Migration, compatibility** |

### Changing in Unity Editor

1. **Edit → Project Settings → Player**
2. Scroll to **"Active Input Handling"**
3. Select one of:
   - Input Manager (Old) - Legacy only
   - Input System Package (New) - New only
   - **Both** - Legacy + New (Recommended during migration)
4. **Restart Unity** (required for changes to take effect)

## Common Input System Error

### InvalidOperationException

**Error Message**:
```
InvalidOperationException: You are trying to read Input using the UnityEngine.Input class,
but you have switched active Input handling to Input System package in Player Settings.
```

**Root Cause**: Code uses `UnityEngine.Input` (legacy) but project configured for new Input System only (`activeInputHandler: 1`)

**Where It Happens**:
```csharp
// This code causes the error when activeInputHandler = 1
Vector3 mousePos = Input.mousePosition;  // Legacy API
if (Input.GetMouseButtonDown(0)) { }      // Legacy API
```

**Solutions**:

#### Option 1: Enable Both Systems (Recommended)
Change `activeInputHandler` to `2`:

```yaml
# Before
activeInputHandler: 1

# After
activeInputHandler: 2  # Enables both systems
```

**Why this is best**:
- No code changes required
- Backward compatible
- Gradual migration possible
- UI system (EventSystem) works with both

#### Option 2: Rewrite Code for New Input System
Migrate to new API:

```csharp
using UnityEngine.InputSystem;

private void HandleInput()
{
    // New Input System API
    if (Keyboard.current == null) return;

    if (Keyboard.current.wKey.isPressed)
    {
        MoveForward();
    }

    if (Mouse.current != null && Mouse.current.leftButton.wasPressedThisFrame)
    {
        Shoot();
    }
}
```

**Benefits**:
- Modern, flexible system
- Better for complex input
- Future-proof

**Drawbacks**:
- Requires code rewrite
- More complex setup
- Breaking change

#### Option 3: Revert to Legacy Only
```yaml
activeInputHandler: 0  # Legacy Input Manager only
```

**Not recommended** - Legacy system is deprecated

## API Comparison

### Keyboard Input

| Action | Legacy Input | New Input System |
|--------|--------------|------------------|
| Check if key pressed | `Input.GetKey(KeyCode.W)` | `Keyboard.current.wKey.isPressed` |
| Key pressed this frame | `Input.GetKeyDown(KeyCode.W)` | `Keyboard.current.wKey.wasPressedThisFrame` |
| Key released this frame | `Input.GetKeyUp(KeyCode.W)` | `Keyboard.current.wKey.wasReleasedThisFrame` |
| Any key pressed | `Input.anyKey` | `Keyboard.current.anyKey.isPressed` |

### Mouse Input

| Action | Legacy Input | New Input System |
|--------|--------------|------------------|
| Mouse position | `Input.mousePosition` | `Mouse.current.position.ReadValue()` |
| Left button | `Input.GetMouseButton(0)` | `Mouse.current.leftButton.isPressed` |
| Left button down | `Input.GetMouseButtonDown(0)` | `Mouse.current.leftButton.wasPressedThisFrame` |
| Right button | `Input.GetMouseButton(1)` | `Mouse.current.rightButton.isPressed` |
| Middle button | `Input.GetMouseButton(2)` | `Mouse.current.middleButton.isPressed` |
| Scroll wheel | `Input.mouseScrollDelta` | `Mouse.current.scroll.ReadValue()` |

### Axis Input

| Action | Legacy Input | New Input System |
|--------|--------------|------------------|
| Horizontal axis | `Input.GetAxis("Horizontal")` | Use Input Actions or manual key checks |
| Vertical axis | `Input.GetAxis("Vertical")` | Use Input Actions or manual key checks |

**Note**: New Input System requires Input Action Assets for axis input. More powerful but more setup.

## Migration Path

### Phase 1: Support Both (Current State)
```yaml
activeInputHandler: 2
```

**Actions**:
- Keep existing legacy code working
- Start writing new features with new Input System
- Test both systems work together
- No breaking changes

### Phase 2: Gradual Migration

**Strategy**:
1. Create abstraction layer (optional but helpful)
2. Migrate one script at a time
3. Test thoroughly after each migration
4. Keep `activeInputHandler: 2` during transition

**Example Abstraction**:
```csharp
public static class GameInput
{
    public static Vector3 MousePosition
    {
        get
        {
            #if ENABLE_INPUT_SYSTEM
                return Mouse.current?.position.ReadValue() ?? Vector3.zero;
            #else
                return Input.mousePosition;
            #endif
        }
    }

    public static bool LeftMouseDown
    {
        get
        {
            #if ENABLE_INPUT_SYSTEM
                return Mouse.current?.leftButton.wasPressedThisFrame ?? false;
            #else
                return Input.GetMouseButtonDown(0);
            #endif
        }
    }
}
```

### Phase 3: Full Migration (Future)

```yaml
activeInputHandler: 1  # New system only
```

**Requirements**:
- All code uses new Input System
- No legacy `Input` API calls
- Input Actions configured
- Thoroughly tested

## Device Null Checking

**Critical**: Always null-check device references in new Input System

```csharp
// ❌ BAD - Will crash if device not present
if (Keyboard.current.spaceKey.isPressed)
{
    Jump();
}

// ✓ GOOD - Safe null checking
if (Keyboard.current != null && Keyboard.current.spaceKey.isPressed)
{
    Jump();
}

// ✓ BETTER - Cache and check
private Keyboard keyboard;

void Update()
{
    if (keyboard == null)
    {
        keyboard = Keyboard.current;
        if (keyboard == null) return;
    }

    if (keyboard.spaceKey.isPressed)
    {
        Jump();
    }
}
```

## Input Actions (Advanced)

For complex input scenarios, use Input Action Assets:

### Creating Input Actions

1. **Create Asset**: Right-click in Project → Create → Input Actions
2. **Define Actions**: Add action maps, actions, and bindings
3. **Generate C# Class**: Check "Generate C# Class" in Inspector
4. **Use in Scripts**:

```csharp
using UnityEngine;
using UnityEngine.InputSystem;

public class PlayerController : MonoBehaviour
{
    private PlayerInputActions inputActions;

    void Awake()
    {
        inputActions = new PlayerInputActions();
        inputActions.Player.Move.performed += OnMove;
        inputActions.Player.Jump.performed += OnJump;
    }

    void OnEnable()
    {
        inputActions.Enable();
    }

    void OnDisable()
    {
        inputActions.Disable();
    }

    private void OnMove(InputAction.CallbackContext context)
    {
        Vector2 moveInput = context.ReadValue<Vector2>();
        // Handle movement
    }

    private void OnJump(InputAction.CallbackContext context)
    {
        // Handle jump
    }
}
```

**Benefits**:
- Clean, event-driven code
- Easy rebinding
- Cross-platform support
- Separates input from logic

## UI and EventSystem

Unity's UI system (UGUI) works with both input systems:

### Legacy Input Manager
```csharp
// Uses StandaloneInputModule (automatically configured)
UnityEngine.EventSystems.StandaloneInputModule
```

### New Input System
```csharp
// Replace with InputSystemUIInputModule
// Add to EventSystem GameObject
using UnityEngine.InputSystem.UI;

// Unity automatically adds this when new Input System active
```

**Both systems support**:
- Button clicks
- Scroll views
- Sliders
- Toggle interactions
- Navigation

## Best Practices

### Do's
✅ Check `activeInputHandler` before writing input code
✅ Null-check devices in new Input System
✅ Use `activeInputHandler: 2` during migration
✅ Create abstraction layer for easy switching
✅ Test input on target platforms
✅ Document which input system your project uses

### Don'ts
❌ Mix APIs without setting `activeInputHandler: 2`
❌ Forget to restart Unity after changing input settings
❌ Use legacy Input System for new projects
❌ Skip null checks for devices
❌ Hard-code input keys (use Input Actions)

## Troubleshooting

### Input Not Working

**Check**:
1. Is `activeInputHandler` configured correctly?
2. Are you using the right API for your configuration?
3. For new Input System: Are devices null-checked?
4. For Input Actions: Are they enabled?
5. For UI: Is EventSystem present and configured?

### Build Errors

**Error**: `The type or namespace name 'InputSystem' could not be found`

**Solution**: Install Input System package via Package Manager

```json
// Packages/manifest.json
{
  "dependencies": {
    "com.unity.inputsystem": "1.7.0"
  }
}
```

### Performance Issues

**New Input System** can be more performant for:
- Many input devices
- Complex input scenarios
- Event-driven architectures

**Legacy Input Manager** may be simpler for:
- Prototypes
- Simple games
- Fewer input sources

## Package Management

### Installing New Input System

1. **Window → Package Manager**
2. Search for "Input System"
3. Click **Install**
4. Unity prompts to enable new Input System → Select "Yes" → Restart

### Checking Package

```json
// Packages/manifest.json
{
  "dependencies": {
    "com.unity.inputsystem": "1.7.0"
  }
}
```

## Additional Resources

- [Unity Manual - Input System](https://docs.unity3d.com/Packages/com.unity.inputsystem@latest)
- [Migration Guide](https://docs.unity3d.com/Packages/com.unity.inputsystem@latest/manual/Migration.html)
- [Input Actions Documentation](https://docs.unity3d.com/Packages/com.unity.inputsystem@latest/manual/Actions.html)
- [Quick Start Guide](https://docs.unity3d.com/Packages/com.unity.inputsystem@latest/manual/QuickStartGuide.html)
