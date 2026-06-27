# Universal Render Pipeline (URP) Setup

## Overview

Universal Render Pipeline (URP) is Unity's modern, performant render pipeline. It requires additional configuration compared to the built-in render pipeline, especially for cameras and lighting.

## Render Pipeline Comparison

| Feature | Built-in RP | URP | HDRP |
|---------|------------|-----|------|
| **Performance** | Moderate | High | Moderate (high-end) |
| **Platforms** | All | All | High-end only |
| **Camera setup** | Simple | Requires URP data | Requires HD data |
| **Lighting** | Traditional | Scriptable | Advanced |
| **Target** | Legacy | Mobile/Cross-platform | High-end PC/Console |

## Common URP Camera Error

### Camera Data is Null

**Error Message**:
```
Camera data is null. Please ensure the render pipeline is correctly initialized
and the camera has a UniversalAdditionalCameraData component.
```

**Root Cause**: Camera's renderer index set to `-1` (invalid) in URP scene

**Location**: `.unity` scene file

**Problematic Configuration**:
```yaml
--- !u!20 &1234567890
Camera:
  m_GameObject: {fileID: 1234567889}
  m_Enabled: 1
  m_ClearFlags: 1
  m_BackGroundColor: {r: 0.19215687, g: 0.3019608, b: 0.4745098, a: 0}
  m_projectionMatrixMode: 1
  m_RendererIndex: -1  # ❌ INVALID - causes error
```

**Solution**: Change `m_RendererIndex` from `-1` to `0`

```yaml
m_RendererIndex: 0  # ✅ Valid - uses first renderer in URP asset
```

### Why This Happens

When creating cameras manually (outside Unity Editor):
- Default renderer index may be `-1`
- URP requires valid renderer index (usually `0`)
- Built-in RP ignores this field

**Best Practice**: Always create cameras via Unity Editor when using URP

## URP Project Setup

### 1. Install URP Package

**Via Package Manager**:
1. **Window → Package Manager**
2. Search for "Universal RP"
3. Click **Install**

**Via manifest.json**:
```json
{
  "dependencies": {
    "com.unity.render-pipelines.universal": "14.0.8"
  }
}
```

### 2. Create URP Asset

**Create Pipeline Asset**:
1. Right-click in Project → **Create → Rendering → URP Asset (with Universal Renderer)**
2. Names generated:
   - `UniversalRenderPipelineAsset.asset` (main asset)
   - `UniversalRenderPipelineAsset_Renderer.asset` (renderer)

**Or create separately**:
```
Create → Rendering → URP Asset
Create → Rendering → URP Forward Renderer
```

### 3. Assign URP Asset

**Edit → Project Settings → Graphics**
- Scriptable Render Pipeline Settings: Assign your URP asset

**Edit → Project Settings → Quality**
- For each quality level: Assign URP asset (or leave default)

### 4. Verify Setup

Check that:
- ✅ URP package installed
- ✅ URP asset created
- ✅ Graphics settings point to URP asset
- ✅ Renderer assigned in URP asset
- ✅ Scene has at least one light (URP handles lighting differently)

## Camera Setup in URP

### Via Unity Editor (Recommended)

**Create Main Camera**:
1. **GameObject → Camera**
2. Unity automatically adds:
   - `Camera` component
   - `UniversalAdditionalCameraData` component
   - Correct renderer index

**Properties**:
```csharp
// UniversalAdditionalCameraData added automatically
// m_RendererIndex set to 0 by default
// Camera configured for URP
```

### Manual Camera Configuration

If creating cameras programmatically:

```csharp
using UnityEngine;
using UnityEngine.Rendering.Universal;

public class CameraSetup : MonoBehaviour
{
    void CreateURPCamera()
    {
        GameObject cameraObj = new GameObject("Main Camera");
        Camera cam = cameraObj.AddComponent<Camera>();

        // Add URP camera data (required for URP)
        UniversalAdditionalCameraData cameraData = cameraObj.AddComponent<UniversalAdditionalCameraData>();

        // Configure camera
        cam.clearFlags = CameraClearFlags.Skybox;
        cam.backgroundColor = new Color(0.19f, 0.30f, 0.47f);

        // Tag as main camera
        cameraObj.tag = "MainCamera";
    }
}
```

### Camera Stacking in URP

URP supports camera stacking for overlay effects:

```csharp
// Base camera
Camera baseCamera = mainCameraObject.GetComponent<Camera>();
UniversalAdditionalCameraData baseCameraData = baseCamera.GetUniversalAdditionalCameraData();
baseCameraData.renderType = CameraRenderType.Base;

// Overlay camera (UI, effects, etc.)
Camera overlayCamera = uiCameraObject.GetComponent<Camera>();
UniversalAdditionalCameraData overlayCameraData = overlayCamera.GetUniversalAdditionalCameraData();
overlayCameraData.renderType = CameraRenderType.Overlay;

// Add overlay to base camera stack
baseCameraData.cameraStack.Add(overlayCamera);
```

**Use Cases**:
- UI rendering on separate layer
- Post-processing effects
- Split-screen multiplayer
- Picture-in-picture

## URP Renderer Settings

### Forward Renderer

**Location**: URP Renderer Asset

**Key Settings**:
- **Rendering Path**: Forward/Deferred
- **Depth Texture**: Enable for effects that need depth
- **Opaque Texture**: Enable for effects that need scene color
- **Native RenderPass**: Performance optimization (mobile)

**Example**:
```csharp
// Access renderer settings
UniversalRenderPipelineAsset urpAsset = GraphicsSettings.currentRenderPipeline as UniversalRenderPipelineAsset;
ScriptableRenderer renderer = urpAsset.scriptableRenderer;
```

### Render Features

Add custom render passes:

1. Open **URP Renderer Asset**
2. **Add Renderer Feature**
3. Choose feature (SSAO, Decals, etc.)

**Common Features**:
- Screen Space Ambient Occlusion (SSAO)
- Decals
- Custom render passes

## Lighting in URP

### Light Types

| Light Type | Use Case | Performance |
|-----------|----------|-------------|
| Directional | Sun/Moon, outdoor scenes | Low cost |
| Point | Torches, lamps, explosions | Medium cost |
| Spot | Flashlights, streetlights | Medium cost |
| Area | Baked lighting only | N/A (baked) |

### Shadows

**Per-Light Settings**:
```csharp
Light light = GetComponent<Light>();
light.shadows = LightShadows.Soft;  // None, Hard, Soft
light.shadowStrength = 1.0f;        // 0-1
light.shadowBias = 0.05f;           // Reduce shadow acne
light.shadowNormalBias = 0.4f;      // Reduce peter-panning
```

**Global Settings** (URP Asset):
- Main Light: Casts shadows
- Additional Lights: Per-pixel or per-vertex
- Shadow Resolution: 256/512/1024/2048/4096
- Shadow Distance: Max distance for shadows

### Baked Lighting

For static objects:

1. Mark objects as **Static** (Lighting Static flag)
2. **Window → Rendering → Lighting**
3. Configure:
   - Lightmap Resolution
   - Lightmap Size
   - Directional Mode
4. Click **Generate Lighting**

**Benefits**:
- Better performance
- High-quality shadows/GI
- No runtime cost

## Post-Processing in URP

### Setup

1. **Install Post-Processing package** (if not included):
```json
{
  "dependencies": {
    "com.unity.postprocessing": "3.2.2"
  }
}
```

2. **Add Volume component**:
```
GameObject → Volume → Global Volume
```

3. **Create Volume Profile**:
```
Create → Volume Profile (URP)
```

4. **Add Overrides**:
   - Bloom
   - Color Grading
   - Vignette
   - Depth of Field
   - Motion Blur
   - etc.

### Example: Bloom

```csharp
using UnityEngine.Rendering;
using UnityEngine.Rendering.Universal;

public class PostProcessingSetup : MonoBehaviour
{
    void SetupBloom()
    {
        Volume volume = GetComponent<Volume>();
        if (volume.profile.TryGet<Bloom>(out var bloom))
        {
            bloom.intensity.value = 0.3f;
            bloom.threshold.value = 1.0f;
            bloom.scatter.value = 0.7f;
        }
    }
}
```

## Material Upgrade

When switching from Built-in to URP:

### Automatic Upgrade

**Edit → Render Pipeline → URP → Upgrade Project Materials to URP Materials**

- Converts Standard shaders to URP Lit
- May need manual adjustment

### Manual Material Setup

```csharp
// Built-in Standard shader
Shader "Standard"

// URP equivalent
Shader "Universal Render Pipeline/Lit"
```

**Common Shaders**:
- `Standard` → `URP/Lit`
- `Standard (Specular)` → `URP/Lit` (change workflow)
- `Unlit` → `URP/Unlit`
- `Particles/Standard` → `URP/Particles/Lit`

## Performance Optimization

### URP Asset Settings

**Rendering**:
- **Render Scale**: <1.0 for performance (0.5 = half resolution)
- **MSAA**: Off/2x/4x/8x (mobile: 2x max)
- **HDR**: Disable if not needed
- **Depth Texture**: Disable if not needed

**Lighting**:
- **Main Light**: Shadow casting
- **Additional Lights**: Per-vertex is cheaper
- **Max Lights**: Reduce for better performance
- **Shadow Distance**: Lower is better

**Shadows**:
- **Shadow Resolution**: Lower for performance
- **Cascade Count**: 1 or 2 for mobile
- **Soft Shadows**: Disable for performance

### Mobile Optimization

```csharp
// Mobile-specific settings
urpAsset.renderScale = 0.75f;         // Slight resolution reduction
urpAsset.msaaSampleCount = 2;         // 2x MSAA (not 4x/8x)
urpAsset.shadowDistance = 30f;        // Shorter shadow distance
urpAsset.shadowCascadeCount = 1;      // Single cascade
urpAsset.supportsHDR = false;         // Disable HDR
```

## Common URP Issues

### Scene Too Dark

**Causes**:
- No lights in scene
- Lights not configured for URP
- Environment lighting disabled
- Materials not URP-compatible

**Solutions**:
1. Add Directional Light (sun)
2. Enable **Window → Rendering → Lighting → Environment**
3. Set Environment Lighting Source
4. Upgrade materials to URP shaders

### Pink Materials

**Cause**: Shader not compatible with URP

**Solution**:
1. Select material
2. Change shader to URP equivalent
3. Or run automatic upgrade tool

### Performance Issues

**Check**:
- Render scale too high
- Too many lights
- Shadows too detailed
- Post-processing too expensive
- MSAA too high

**Profile**:
- **Window → Analysis → Profiler**
- Check "Rendering" section
- Identify bottlenecks

## URP vs HDRP

| Feature | URP | HDRP |
|---------|-----|------|
| **Target** | Mobile, cross-platform | High-end PC/Console |
| **Performance** | Optimized | Demanding |
| **Features** | Essential | Advanced (ray tracing, etc.) |
| **Complexity** | Moderate | High |
| **File Size** | Smaller | Larger |

**Choose URP when**:
- Targeting mobile
- Want good performance
- Need cross-platform support
- Moderate visual quality sufficient

**Choose HDRP when**:
- High-end PC/console only
- Need cutting-edge visuals
- Ray tracing required
- Performance secondary

## Debugging URP

### Check URP Status

```csharp
using UnityEngine.Rendering;
using UnityEngine.Rendering.Universal;

public class URPDebug : MonoBehaviour
{
    void Start()
    {
        // Check if URP active
        if (GraphicsSettings.currentRenderPipeline is UniversalRenderPipelineAsset urpAsset)
        {
            Debug.Log("URP is active");
            Debug.Log($"Renderer: {urpAsset.scriptableRenderer}");
            Debug.Log($"MSAA: {urpAsset.msaaSampleCount}");
        }
        else
        {
            Debug.LogWarning("URP is not active!");
        }
    }
}
```

### Camera Diagnostics

```csharp
using UnityEngine.Rendering.Universal;

void DiagnoseCamera(Camera cam)
{
    UniversalAdditionalCameraData cameraData = cam.GetUniversalAdditionalCameraData();

    if (cameraData == null)
    {
        Debug.LogError($"Camera {cam.name} missing UniversalAdditionalCameraData!");
        return;
    }

    Debug.Log($"Camera: {cam.name}");
    Debug.Log($"Render Type: {cameraData.renderType}");
    Debug.Log($"Render Post Processing: {cameraData.renderPostProcessing}");
    Debug.Log($"Anti-aliasing: {cameraData.antialiasing}");
}
```

## Additional Resources

- [URP Documentation](https://docs.unity3d.com/Packages/com.unity.render-pipelines.universal@latest)
- [URP vs HDRP Comparison](https://unity.com/srp/choosing-a-render-pipeline)
- [Upgrading to URP](https://docs.unity3d.com/Packages/com.unity.render-pipelines.universal@latest/manual/InstallURPIntoAProject.html)
- [Camera Stacking](https://docs.unity3d.com/Packages/com.unity.render-pipelines.universal@latest/manual/camera-stacking.html)
