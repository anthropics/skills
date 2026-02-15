# Common Unity Errors Catalog

## Overview

This document catalogs common Unity errors with their causes, solutions, and prevention strategies. Search by error message or keyword to quickly find solutions.

---

## GUID and Meta File Errors

### Could not extract GUID

**Error**:
```
Could not extract GUID in text file Assets/Prefabs/MyPrefab.prefab at line 97.
```

**Cause**: Invalid GUID format (non-hexadecimal characters)

**Solution**:
1. Find correct GUID: `grep "^guid:" Assets/Scripts/MyScript.cs.meta`
2. Replace invalid GUID in prefab file
3. Ensure GUID is 32 hexadecimal characters (0-9, a-f)

**Prevention**: Never manually create GUIDs; always copy from `.meta` files

→ See `reference/guid-system.md` for details

### Broken PPtr

**Error**:
```
Broken PPtr [guid 1234...] in file Assets/Scenes/MyScene.unity
```

**Cause**: Reference to deleted asset (orphaned `.meta` file)

**Solution**:
```bash
# Find and remove orphaned meta files
for meta in Assets/**/*.meta; do
    [ -f "${meta%.meta}" ] || git rm "$meta"
done
```

**Prevention**: Delete files via Unity Editor or delete both `.cs` and `.meta` together

→ See `reference/guid-system.md` for details

---

## Input System Errors

### InvalidOperationException: Input System

**Error**:
```
InvalidOperationException: You are trying to read Input using the UnityEngine.Input class,
but you have switched active Input handling to Input System package in Player Settings.
```

**Cause**: Using legacy Input API when project configured for new Input System only

**Solution**:
Change `activeInputHandler` to `2` (Both) in `ProjectSettings/ProjectSettings.asset`:
```yaml
activeInputHandler: 2
```

Or via Editor: **Edit → Project Settings → Player → Active Input Handling → Both**

**Prevention**: Check Input System configuration before writing input code

→ See `reference/input-systems.md` for details

### Keyboard.current is null

**Error**: NullReferenceException when accessing `Keyboard.current`

**Cause**: Keyboard device not connected or not initialized

**Solution**:
```csharp
// Always null-check devices
if (Keyboard.current != null && Keyboard.current.spaceKey.wasPressedThisFrame)
{
    Jump();
}
```

**Prevention**: Always null-check device references in new Input System

→ See `reference/input-systems.md` for details

---

## URP Errors

### Camera data is null

**Error**:
```
Camera data is null. Please ensure the render pipeline is correctly initialized
and the camera has a UniversalAdditionalCameraData component.
```

**Cause**: Camera's `m_RendererIndex` set to `-1` (invalid) in URP scene

**Solution**:
Change in `.unity` scene file:
```yaml
m_RendererIndex: 0  # Changed from -1
```

**Prevention**: Always create cameras via Unity Editor when using URP

→ See `reference/urp-setup.md` for details

### Pink Materials (Shader Error)

**Symptom**: Materials appear bright pink/magenta

**Cause**: Shader not compatible with active render pipeline

**Solution**:
1. **Automatic**: Edit → Render Pipeline → URP → Upgrade Project Materials
2. **Manual**: Change shader to URP equivalent
   - `Standard` → `Universal Render Pipeline/Lit`
   - `Unlit` → `Universal Render Pipeline/Unlit`

**Prevention**: Use URP-compatible shaders from the start

→ See `reference/urp-setup.md` for details

---

## Physics Errors

### Objects fall through floor

**Symptom**: Rigidbody objects pass through colliders

**Causes**:
- Fast-moving objects (tunneling)
- Collider too thin
- Layer collision matrix disabled
- Missing Rigidbody

**Solutions**:
1. Use Continuous Collision Detection:
   ```csharp
   rb.collisionDetectionMode = CollisionDetectionMode.Continuous;
   ```
2. Increase collider thickness
3. Check layer collision matrix (**Edit → Project Settings → Physics**)
4. Use triggers for fast objects

**Prevention**: Use appropriate collision detection mode for object speed

→ See `reference/physics-system.md` for details

### Triggers not detecting

**Symptom**: `OnTriggerEnter` not called

**Causes**:
- No Rigidbody on either object
- Layer collision matrix disabled
- `IsTrigger` not set to true
- Callback method misspelled

**Solutions**:
1. Add Rigidbody to at least one object
2. Verify layer collision matrix enabled
3. Check collider has `IsTrigger = true`
4. Verify method signature exact: `void OnTriggerEnter(Collider other)`

**Prevention**: Ensure at least one Rigidbody present for trigger detection

→ See `reference/physics-system.md` for details

---

## NullReferenceException Errors

### Unassigned SerializeField

**Error**:
```
NullReferenceException: Object reference not set to an instance of an object
ComponentName.MethodName () (at Assets/Scripts/ComponentName.cs:42)
```

**Cause**: `[SerializeField]` field not assigned in Inspector

**Example**:
```csharp
[SerializeField] private Transform targetTransform;  // Not assigned!

void Start()
{
    Vector3 pos = targetTransform.position;  // ← Throws here
}
```

**Solutions**:
1. Assign field in Inspector
2. Add null check:
   ```csharp
   if (targetTransform == null)
   {
       Debug.LogError("Target not assigned!");
       return;
   }
   ```
3. Use `OnValidate`:
   ```csharp
   void OnValidate()
   {
       if (targetTransform == null)
           Debug.LogWarning($"{name}: Target not assigned!");
   }
   ```

**Prevention**: Always assign SerializeField references or add null checks

### GetComponent returns null

**Error**: NullReferenceException after GetComponent

**Cause**: Component doesn't exist on GameObject

**Solution**:
```csharp
// ❌ Unsafe
Rigidbody rb = GetComponent<Rigidbody>();
rb.velocity = Vector3.zero;  // Crash if no Rigidbody!

// ✓ Safe
if (TryGetComponent<Rigidbody>(out var rb))
{
    rb.linearVelocity = Vector3.zero;
}
else
{
    Debug.LogError("Rigidbody not found!");
}
```

**Prevention**: Use `TryGetComponent` or null-check `GetComponent` results

---

## Resources Loading Errors

### Resources.Load returns null

**Error**: Resources.Load returns null, file exists but not loading

**Cause**: File not in `Assets/Resources/` folder

**Solution**:
1. Create `Assets/Resources/` folder structure
2. Move files into Resources folder
3. Load without extension or path prefix:
   ```csharp
   // File at: Assets/Resources/Data/config.json
   TextAsset data = Resources.Load<TextAsset>("Data/config");
   ```

**Prevention**: Understand `Resources.Load()` only works with Resources folders

---

## Compiler Warnings (Treat as Errors)

### CS0414: Field assigned but never used

**Warning**:
```
Assets/Scripts/MyScript.cs(19,25): warning CS0414:
The field 'MyScript.myField' is assigned but its value is never used
```

**Cause**: SerializeField declared but never accessed in code

**Solution**: Actually use the field in your logic:
```csharp
[SerializeField] private float speed = 5f;

void Update()
{
    // Use the field!
    transform.position += transform.forward * speed * Time.deltaTime;
}
```

**Prevention**: Use fields immediately after declaration; test Inspector changes

### CS0649: Field never assigned

**Warning**:
```
warning CS0649: Field 'MyClass.myField' is never assigned to,
and will always have its default value null
```

**Cause**: Private field without `[SerializeField]` that's never assigned in code

**Solution**:
1. Add `[SerializeField]` if assigning in Inspector
2. Or assign in code
3. Or remove if unused

---

## Build Errors

### Scripts have compiler errors

**Error**: Cannot build due to compiler errors

**Cause**: Syntax errors, missing namespaces, or API mismatches

**Solution**:
1. Open Console (**Window → General → Console**)
2. Fix all red errors
3. Clear all yellow warnings (treat them seriously!)
4. Verify script compiles: **Assets → Reimport All**

### Missing assembly references

**Error**:
```
error CS0246: The type or namespace name 'InputSystem' could not be found
```

**Cause**: Missing package or assembly reference

**Solution**:
1. Install required package via Package Manager
2. Add assembly reference in .asmdef (if using assembly definitions)
3. Check `using` statements

---

## API Deprecation Warnings

### Rigidbody.velocity is obsolete

**Warning**:
```
'Rigidbody.velocity' is obsolete: 'Use linearVelocity instead.'
```

**Cause**: Using deprecated API in Unity 2023.1+

**Solution**:
```csharp
// Old (pre-2023.1)
rb.velocity = Vector3.forward;

// New (2023.1+)
rb.linearVelocity = Vector3.forward;
```

**Prevention**: Keep up with Unity API changes when upgrading versions

→ See `reference/physics-system.md` for details

---

## Performance Warnings

### Too many vertices in mesh

**Warning**: Mesh has excessive vertex count

**Solution**:
1. Reduce polygon count in 3D software
2. Use LOD (Level of Detail) system
3. Enable mesh compression

### Too many draw calls

**Symptom**: Low framerate, many draw calls in Profiler

**Solution**:
1. Enable **Static Batching** (mark objects static)
2. Use **GPU Instancing** on materials
3. Combine meshes
4. Use texture atlases

---

## Platform-Specific Errors

### Android Build Failed

**Common causes**:
- Missing Android SDK/NDK
- Incorrect API level
- Keystore issues
- Permissions not set

**Solution**:
1. **Edit → Preferences → External Tools** → Set Android SDK/NDK
2. **Player Settings → Android** → Set minimum API level
3. Configure keystore
4. Add required permissions in manifest

### iOS Build Failed

**Common causes**:
- Xcode not installed
- Invalid bundle identifier
- Missing capabilities
- Code signing issues

**Solution**:
1. Install latest Xcode
2. Set valid bundle identifier
3. Configure capabilities in Xcode project
4. Set up code signing

---

## Debugging Strategies

### General Approach

1. **Read the full error message** - often contains the solution
2. **Note the line number** - error location is critical
3. **Check recent changes** - what changed before the error?
4. **Google the exact error** - likely someone else solved it
5. **Check Unity Forums** - official community support
6. **Profile if performance** - use Unity Profiler

### Console Tools

```csharp
// Basic logging
Debug.Log("Value: " + value);

// Warnings and errors
Debug.LogWarning("This might be a problem");
Debug.LogError("This is definitely wrong");

// Conditional logging
Debug.Assert(value != null, "Value should not be null!");

// Context logging (clickable in Console)
Debug.Log("Object info", gameObject);
```

### Break on Error

**Edit → Preferences → General → Error Pause**
- Enable to pause Editor when error occurs
- Helpful for debugging runtime errors

---

## Quick Reference: Error Keywords

| Error Keyword | Common Cause | Quick Fix |
|--------------|--------------|-----------|
| GUID | Invalid or missing GUID | Copy from `.meta` file |
| Input System | API mismatch | Set `activeInputHandler: 2` |
| Camera data is null | URP renderer index | Set `m_RendererIndex: 0` |
| NullReferenceException | Unassigned field | Assign in Inspector or null-check |
| Resources.Load | Wrong folder | Move to `Resources/` folder |
| velocity obsolete | Old API (2023.1+) | Use `linearVelocity` |
| CS0414 | Unused field | Actually use the field |
| Pink material | Wrong shader | Use URP shaders |
| Trigger not working | Missing Rigidbody | Add Rigidbody component |
| Broken PPtr | Orphaned meta file | Remove orphaned `.meta` |

---

## Additional Resources

- [Unity Documentation](https://docs.unity3d.com/)
- [Unity Forums](https://forum.unity.com/)
- [Unity Answers](https://answers.unity.com/)
- [Stack Overflow - Unity Tag](https://stackoverflow.com/questions/tagged/unity3d)
- [Unity Issue Tracker](https://issuetracker.unity3d.com/)
