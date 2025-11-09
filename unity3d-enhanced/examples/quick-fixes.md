# Unity Quick Fixes Reference

This guide provides quick, copy-paste solutions for common Unity problems. For detailed explanations, see the reference files.

---

## Input System Issues

### Fix: Input System Exception

**Error**: `InvalidOperationException: You are trying to read Input using the UnityEngine.Input class...`

**One-line fix**: Change in `ProjectSettings/ProjectSettings.asset`:
```yaml
activeInputHandler: 2  # Enable both input systems
```

**Via Editor**: Edit → Project Settings → Player → Active Input Handling → **Both** → Restart Unity

→ Details: `reference/input-systems.md`

---

## GUID Errors

### Fix: Invalid GUID in Prefab

**Error**: `Could not extract GUID in text file Assets/Prefabs/MyPrefab.prefab`

**Quick fix**:
```bash
# 1. Find correct GUID
grep "^guid:" Assets/Scripts/MyScript.cs.meta

# 2. Replace in prefab file
# Old: guid: a1b2c3d4e5f6g7h8i9j0k1l2m3n4o5p6
# New: guid: 6004172616168c346951d6f4cddd83da (from step 1)
```

→ Details: `reference/guid-system.md`

### Fix: Orphaned Meta Files

**Error**: `Broken PPtr [guid]...`

**Quick fix**:
```bash
# Find and remove orphaned .meta files
for meta in Assets/**/*.meta; do
    [ -f "${meta%.meta}" ] || git rm "$meta"
done
```

→ Details: `reference/guid-system.md`

---

## URP Issues

### Fix: Camera Data is Null

**Error**: `Camera data is null. Please ensure the render pipeline is correctly initialized...`

**Quick fix**: Change in `.unity` scene file (search for camera):
```yaml
m_RendererIndex: 0  # Changed from -1
```

**Or create new camera**: GameObject → Camera (Unity handles setup automatically)

→ Details: `reference/urp-setup.md`

### Fix: Pink Materials

**Symptom**: Materials appear bright pink/magenta

**Quick fix**: Edit → Render Pipeline → URP → **Upgrade Project Materials to URP Materials**

**Or manually**: Change shader from `Standard` to `Universal Render Pipeline/Lit`

→ Details: `reference/urp-setup.md`

---

## Physics Issues

### Fix: Bullets Missing Targets

**Problem**: Fast bullets pass through colliders

**Quick fix**: Use **triggers** on targets:
```csharp
// Target script
private void OnTriggerEnter(Collider other)
{
    if (other.gameObject.layer == bulletLayer)
    {
        Explode();
    }
}
```

**Setup**:
- Target: `IsTrigger = true`, needs Rigidbody
- Bullet: Solid collider, Rigidbody with velocity

→ Details: `reference/physics-system.md`

### Fix: Triggers Not Detecting

**Problem**: `OnTriggerEnter` never called

**Quick fix checklist**:
- [ ] At least one object has Rigidbody
- [ ] Collider has `IsTrigger = true`
- [ ] Layer collision matrix enabled (Edit → Project Settings → Physics)
- [ ] Method signature exact: `void OnTriggerEnter(Collider other)`

→ Details: `reference/physics-system.md`

### Fix: Rigidbody Velocity (Unity 2023.1+)

**Warning**: `'Rigidbody.velocity' is obsolete...`

**Quick fix**: Find & Replace
```csharp
// Find:    rb.velocity
// Replace: rb.linearVelocity
```

→ Details: `reference/physics-system.md`

---

## NullReferenceException Fixes

### Fix: Unassigned SerializeField

**Error**: `NullReferenceException` at line using SerializeField

**Quick fix**: Add null check
```csharp
[SerializeField] private Transform target;

void Start()
{
    if (target == null)
    {
        Debug.LogError($"{name}: Target not assigned!");
        return;
    }
    // Use target safely
}
```

**Better**: Use `OnValidate` to catch at edit-time
```csharp
private void OnValidate()
{
    if (target == null)
        Debug.LogWarning($"{name}: Target not assigned!");
}
```

→ Details: `reference/common-errors.md`

### Fix: GetComponent Returns Null

**Quick fix**: Use `TryGetComponent`
```csharp
// ❌ Unsafe
Rigidbody rb = GetComponent<Rigidbody>();
rb.linearVelocity = Vector3.zero;  // Crash if no Rigidbody!

// ✓ Safe
if (TryGetComponent<Rigidbody>(out var rb))
{
    rb.linearVelocity = Vector3.zero;
}
```

→ Details: `reference/common-errors.md`

---

## Resources Loading

### Fix: Resources.Load Returns Null

**Problem**: File exists but Resources.Load returns null

**Quick fix**: Move file to Resources folder
```
Assets/
  Resources/  ← Must be named exactly "Resources"
    Data/
      config.json  ← Your file here
```

**Load without extension**:
```csharp
// File at: Assets/Resources/Data/config.json
TextAsset data = Resources.Load<TextAsset>("Data/config");
```

→ Details: `reference/common-errors.md`

---

## Compiler Warnings

### Fix: CS0414 (Field Never Used)

**Warning**: `Field 'MyClass.field' is assigned but its value is never used`

**Quick fix**: Actually use the field
```csharp
[SerializeField] private float speed = 5f;

void Update()
{
    // Use it!
    transform.position += transform.forward * speed * Time.deltaTime;
}
```

→ Details: `reference/common-errors.md`

---

## Git and Meta Files

### Quick Commands

```bash
# Check for orphaned .meta files
for meta in Assets/**/*.meta; do
    [ -f "${meta%.meta}" ] || echo "Orphaned: $meta"
done

# Find assets missing .meta files
find Assets -type f ! -name "*.meta" ! -path "*/.*" | while read file; do
    [ -f "$file.meta" ] || echo "Missing .meta: $file"
done

# Stage asset and meta together
git add Assets/NewScript.cs Assets/NewScript.cs.meta

# Remove deleted asset's meta
git rm Assets/DeletedScript.cs.meta
```

→ Details: `reference/guid-system.md`

---

## Code Snippets

### Null-Safe GetComponent

```csharp
// Safe component access pattern
if (TryGetComponent<T>(out var component))
{
    // Use component
}
else
{
    Debug.LogError($"{name} missing {typeof(T)} component!");
}
```

### Input System Device Check

```csharp
// New Input System - always null-check devices
using UnityEngine.InputSystem;

private Keyboard keyboard;

void Update()
{
    if (keyboard == null)
    {
        keyboard = Keyboard.current;
        if (keyboard == null) return;
    }

    if (keyboard.spaceKey.wasPressedThisFrame)
    {
        Jump();
    }
}
```

### Object Pooling Pattern

```csharp
public class ObjectPool : MonoBehaviour
{
    [SerializeField] private GameObject prefab;
    private Queue<GameObject> pool = new Queue<GameObject>();

    public GameObject Get()
    {
        if (pool.Count > 0)
        {
            GameObject obj = pool.Dequeue();
            obj.SetActive(true);
            return obj;
        }
        return Instantiate(prefab);
    }

    public void Return(GameObject obj)
    {
        obj.SetActive(false);
        pool.Enqueue(obj);
    }
}
```

### Trigger Detection with Layers

```csharp
[SerializeField] private LayerMask targetLayers;

private void OnTriggerEnter(Collider other)
{
    // Check if other object is in target layers
    if (((1 << other.gameObject.layer) & targetLayers) != 0)
    {
        // Handle trigger
    }
}
```

### URP Camera Creation

```csharp
using UnityEngine;
using UnityEngine.Rendering.Universal;

void CreateCamera()
{
    GameObject camObj = new GameObject("Main Camera");
    Camera cam = camObj.AddComponent<Camera>();

    // Required for URP
    UniversalAdditionalCameraData cameraData =
        camObj.AddComponent<UniversalAdditionalCameraData>();

    camObj.tag = "MainCamera";
}
```

---

## Project Settings Quick Checks

### Input System Configuration

```bash
# Check current setting
grep "activeInputHandler:" ProjectSettings/ProjectSettings.asset

# Should be:
# activeInputHandler: 0  (Legacy only)
# activeInputHandler: 1  (New only)
# activeInputHandler: 2  (Both - recommended)
```

### URP Verification

```bash
# Check if URP asset assigned
grep "m_CustomRenderPipeline:" ProjectSettings/GraphicsSettings.asset

# Should reference URP asset, not "m_CustomRenderPipeline: {fileID: 0}"
```

### Meta Files Validation

```bash
# Check project configured for text serialization
grep "m_ExternalVersionControlSupport:" ProjectSettings/EditorSettings.asset

# Should be: m_ExternalVersionControlSupport: Visible Meta Files
```

---

## Emergency Troubleshooting

### Nuclear Options (Use with Caution!)

**Clear Library** (forces reimport of all assets):
```bash
# Close Unity first!
rm -rf Library/
# Reopen Unity - will regenerate Library/
```

**Reimport All Assets**:
- Assets → Reimport All
- Use when: Meta files corrupted, import settings broken

**Reset Project Settings**:
- Manually delete `ProjectSettings/` (backup first!)
- Unity regenerates default settings

**Note**: Always backup before using these!

---

## Platform-Specific Quick Fixes

### Android

**Fix: Missing SDK/NDK**
- Edit → Preferences → External Tools → Browse to Android SDK/NDK paths

**Fix: API Level Too Low**
- Player Settings → Android → Minimum API Level → 24 (Android 7.0)

### iOS

**Fix: Bundle Identifier Invalid**
- Player Settings → iOS → Bundle Identifier → `com.company.appname`

**Fix: Missing Camera Permission**
- Player Settings → iOS → Camera Usage Description → "Required for AR features"

---

## Performance Quick Wins

```csharp
// Cache transforms
private Transform myTransform;
void Awake() { myTransform = transform; }

// Use CompareTag instead of ==
if (other.CompareTag("Player"))  // Faster

// Disable cameras you're not using
camera.enabled = false;

// Use object pooling for frequently spawned objects
// (see Object Pooling Pattern above)

// Set Rigidbodies to sleep when idle
rb.Sleep();

// Use layer collision matrix
// Edit → Project Settings → Physics → Layer Collision Matrix
```

---

## Diagnostic Commands

```bash
# Find all invalid GUIDs
grep -Ern "guid: [^0-9a-f]" Assets/

# List all cameras in scenes
grep -n "m_Name: Main Camera" Assets/Scenes/*.unity

# Find all Resources folders
find Assets -type d -name "Resources"

# Check Unity version
grep "m_EditorVersion:" ProjectSettings/ProjectVersion.txt
```

---

## When All Else Fails

1. **Read the error carefully** - the answer is often in the message
2. **Check the line number** - exact location of the problem
3. **Google the exact error** - others have likely solved it
4. **Unity Forums / Stack Overflow** - active communities
5. **Check Unity documentation** - official API reference
6. **Review recent changes** - git diff to see what changed
7. **Start fresh** - create minimal reproduction case

---

## Reference File Index

| Issue Category | Reference File |
|---------------|---------------|
| GUIDs, meta files, asset references | `reference/guid-system.md` |
| Input System, API migration | `reference/input-systems.md` |
| Rigidbody, triggers, collisions | `reference/physics-system.md` |
| URP, cameras, rendering | `reference/urp-setup.md` |
| Common error catalog | `reference/common-errors.md` |
| Project setup, workflows | `reference/project-setup.md` |
