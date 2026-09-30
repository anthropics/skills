# Performance Guide

Profiling, optimization, and mobile-specific patterns for Three.js applications.

---

## Profiling Workflow

**Rule #1**: Profile before optimizing. Never guess at bottlenecks.

### Stats.js (Frame Rate)

```javascript
import Stats from 'three/addons/libs/stats.module.js';

const stats = new Stats();
stats.showPanel(0); // 0=fps, 1=ms, 2=memory
document.body.appendChild(stats.dom);

renderer.setAnimationLoop(() => {
    stats.begin();
    // game loop...
    renderer.render(scene, camera);
    stats.end();
});
```

### renderer.info (GPU Resources)

```javascript
function logInfo() {
    const info = renderer.info;
    console.table({
        'Draw calls': info.render.calls,
        'Triangles': info.render.triangles,
        'Geometries': info.memory.geometries,
        'Textures': info.memory.textures,
        'Programs': info.programs?.length
    });
}

// Call after scene is loaded
// Target: <100 draw calls, <500K triangles for smooth 60fps
```

### Chrome DevTools Performance Tab

1. Open DevTools > Performance
2. Click Record, play for 5 seconds, Stop
3. Look for:
   - Long frames (>16ms = below 60fps)
   - JS execution time vs idle
   - GPU bottleneck (use "GPU" checkbox in timeline)

---

## Draw Call Reduction

Every `Mesh` in the scene = 1 draw call. Draw calls are the #1 performance killer.

### Merge Static Geometries

```javascript
import { mergeGeometries } from 'three/addons/utils/BufferGeometryUtils.js';

// Before: 100 separate meshes = 100 draw calls
const geometries = [];
for (let i = 0; i < 100; i++) {
    const geo = new THREE.BoxGeometry(1, 1, 1);
    geo.translate(i * 2, 0, 0); // Position via geometry, not mesh
    geometries.push(geo);
}

// After: 1 merged mesh = 1 draw call
const merged = mergeGeometries(geometries);
const mesh = new THREE.Mesh(merged, sharedMaterial);
scene.add(mesh);
```

**Limitation**: Merged geometries can't be moved independently. Only use for static scenery.

### InstancedMesh (Dynamic)

```javascript
// 1000 objects, 1 draw call, individually transformable
const mesh = new THREE.InstancedMesh(geometry, material, 1000);

const dummy = new THREE.Object3D();
for (let i = 0; i < 1000; i++) {
    dummy.position.set(Math.random() * 100, 0, Math.random() * 100);
    dummy.updateMatrix();
    mesh.setMatrixAt(i, dummy.matrix);
}

mesh.instanceMatrix.needsUpdate = true;
scene.add(mesh);
```

### BatchedMesh (r170+, Mixed Geometries)

```javascript
// Multiple different geometries, 1 draw call
const batchedMesh = new THREE.BatchedMesh(
    50,     // max geometry count
    5000,   // max vertex count
    10000,  // max index count
    material
);

const boxId = batchedMesh.addGeometry(new THREE.BoxGeometry(1, 1, 1));
const sphereId = batchedMesh.addGeometry(new THREE.SphereGeometry(0.5));

const matrix = new THREE.Matrix4();
matrix.makeTranslation(0, 0, 0);
batchedMesh.addInstance(boxId, matrix);

matrix.makeTranslation(3, 0, 0);
batchedMesh.addInstance(sphereId, matrix);

scene.add(batchedMesh);
```

---

## Level of Detail (LOD)

Switch to simpler geometries at distance:

```javascript
const lod = new THREE.LOD();

// High detail (close)
const highGeo = new THREE.SphereGeometry(1, 32, 16);
lod.addLevel(new THREE.Mesh(highGeo, material), 0);

// Medium detail
const medGeo = new THREE.SphereGeometry(1, 16, 8);
lod.addLevel(new THREE.Mesh(medGeo, material), 20);

// Low detail (far)
const lowGeo = new THREE.SphereGeometry(1, 8, 4);
lod.addLevel(new THREE.Mesh(lowGeo, material), 50);

scene.add(lod);

// LOD updates automatically based on camera distance
// Just make sure to call lod.update(camera) in your loop
// (or use scene.autoUpdate which is true by default)
```

---

## Texture Optimization

### Size Rules
- Power of 2 dimensions: 256, 512, 1024, 2048 (GPU-friendly)
- Don't exceed 2048x2048 for most use cases
- Mobile: stick to 512x512 or 1024x1024

### Compression
```javascript
// Use KTX2 compressed textures for GPU-compressed formats
import { KTX2Loader } from 'three/addons/loaders/KTX2Loader.js';

const ktx2Loader = new KTX2Loader();
ktx2Loader.setTranscoderPath('https://unpkg.com/three@0.170.0/examples/jsm/libs/basis/');
ktx2Loader.detectSupport(renderer);

ktx2Loader.load('texture.ktx2', (texture) => {
    material.map = texture;
    material.needsUpdate = true;
});
```

### Texture Atlas
Combine multiple small textures into one large texture. Reduces texture switches.

```javascript
// Instead of 10 separate textures for 10 objects:
// Use 1 atlas texture and adjust UV coordinates per object
const atlas = textureLoader.load('textures/atlas.png');

// Each object uses a portion of the atlas via UV mapping
```

---

## Frustum Culling

Three.js automatically skips rendering objects outside the camera's view (frustum culling is ON by default). But you can optimize further:

```javascript
// For objects you KNOW are always visible, skip the culling check
alwaysVisibleMesh.frustumCulled = false;

// For large groups of small objects, cull the parent group
// instead of each individual mesh
group.frustumCulled = true;
```

---

## Shadow Optimization

Shadows are expensive. Optimize aggressively:

```javascript
// Limit shadow map size
light.shadow.mapSize.width = 1024;  // Not 4096!
light.shadow.mapSize.height = 1024;

// Tighten shadow camera frustum
light.shadow.camera.near = 0.5;
light.shadow.camera.far = 50;
light.shadow.camera.left = -20;
light.shadow.camera.right = 20;
light.shadow.camera.top = 20;
light.shadow.camera.bottom = -20;

// Only cast shadows from important objects
importantMesh.castShadow = true;
smallDecoration.castShadow = false;  // Not worth it

// Receive shadows only where visible
ground.receiveShadow = true;
sky.receiveShadow = false;
```

---

## Mobile-Specific Optimization

```javascript
const isMobile = /Android|iPhone|iPad|iPod/i.test(navigator.userAgent);

if (isMobile) {
    // Lower pixel ratio
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 1.5));

    // Disable shadows entirely
    renderer.shadowMap.enabled = false;

    // Simpler materials
    // Use MeshPhongMaterial instead of MeshStandardMaterial

    // Reduce geometry detail
    const segments = 16; // Instead of 32+

    // Smaller render size
    const scale = 0.75;
    renderer.setSize(
        window.innerWidth * scale,
        window.innerHeight * scale,
        false
    );
    renderer.domElement.style.width = '100%';
    renderer.domElement.style.height = '100%';
}
```

---

## Object Pooling (Memory Optimization)

Don't create/destroy objects in the game loop. Reuse them:

```javascript
class Pool {
    constructor(createFn, size = 20) {
        this.available = [];
        this.active = [];

        for (let i = 0; i < size; i++) {
            const obj = createFn();
            obj.visible = false;
            this.available.push(obj);
        }
    }

    get() {
        const obj = this.available.pop() || this.createFn();
        obj.visible = true;
        this.active.push(obj);
        return obj;
    }

    release(obj) {
        obj.visible = false;
        const idx = this.active.indexOf(obj);
        if (idx !== -1) this.active.splice(idx, 1);
        this.available.push(obj);
    }
}
```

See also: [game-loop-and-state.md](game-loop-and-state.md) for the full ObjectPool pattern.

---

## Memory Leak Detection

```javascript
// Monitor GPU resources over time
let prevGeometries = 0;
let prevTextures = 0;

function checkForLeaks() {
    const info = renderer.info;
    const geos = info.memory.geometries;
    const texs = info.memory.textures;

    if (geos > prevGeometries + 10) {
        console.warn(`Geometry leak? ${prevGeometries} -> ${geos}`);
    }
    if (texs > prevTextures + 5) {
        console.warn(`Texture leak? ${prevTextures} -> ${texs}`);
    }

    prevGeometries = geos;
    prevTextures = texs;
}

// Call periodically (e.g., every 10 seconds)
setInterval(checkForLeaks, 10000);
```

---

## Performance Budget

Target frame budgets for 60fps:

| Category | Budget |
|----------|--------|
| **Total frame** | <16.6ms |
| Draw calls | <100 |
| Triangles | <500K (desktop), <200K (mobile) |
| Textures in memory | <200MB (desktop), <50MB (mobile) |
| Shadow maps | 1-2 lights max |
| Post-processing passes | 2-3 max |
| Active animations | <50 mixers |

---

## Quick Wins Checklist

1. Cap pixel ratio: `Math.min(window.devicePixelRatio, 2)`
2. Reuse geometries and materials (don't create in loops)
3. Use `InstancedMesh` for 50+ identical objects
4. Merge static geometry with `BufferGeometryUtils`
5. Limit shadow map to 1024x1024
6. Only shadow-cast important objects
7. Dispose everything when removing from scene
8. Use `renderer.info` to track resource counts
9. Compress textures (KTX2) and keep sizes power-of-2
10. On mobile: reduce pixel ratio, disable shadows, simplify materials
