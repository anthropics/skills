---
name: threejs-master
description: >
  The definitive Three.js game-building skill. Scene setup, lighting, geometries, materials,
  animations, controls, GLTF models, game architecture, collision, input, audio, UI, and
  performance optimization. Modern ES modules, Three.js r170+ APIs.
---

# Three.js Master

The definitive skill for creating performant Three.js web applications and games using modern ES module patterns.

## Reference Files

> **Important**: Read the appropriate reference file when working on specific topics.

| Topic | File | Use When |
|-------|------|----------|
| **Coordinate System** | [coordinate-system.md](references/coordinate-system.md) | Axes, GLTF orientation, camera-relative movement |
| **GLTF Models** | [gltf-loading-guide.md](references/gltf-loading-guide.md) | Loading, caching, cloning 3D models, SkeletonUtils |
| **Game Loop & State** | [game-loop-and-state.md](references/game-loop-and-state.md) | State machine, time scaling, game loop, screen effects |
| **Animation** | [animation-guide.md](references/animation-guide.md) | Crossfade, safe selection, facing direction, squash & stretch |
| **Collision & Physics** | [collision-and-physics.md](references/collision-and-physics.md) | AABB, sphere, raycaster, trigger zones, Rapier/Cannon |
| **Input Handling** | [input-handling.md](references/input-handling.md) | Keyboard, gamepad, touch, pointer lock, action mapping |
| **Audio** | [audio-guide.md](references/audio-guide.md) | AudioListener, PositionalAudio, SFX pool, music system |
| **UI Systems** | [ui-systems.md](references/ui-systems.md) | HUD overlays, health bars, menus, loading screens |
| **Scene Management** | [scene-management.md](references/scene-management.md) | Level loading, transitions, dispose patterns, cleanup |
| **Advanced Rendering** | [advanced-rendering.md](references/advanced-rendering.md) | Post-processing, shaders, env maps, instancing, BatchedMesh |
| **Reference Frames** | [reference-frame-contract.md](references/reference-frame-contract.md) | Calibration, anchoring, axis correctness, debugging |
| **Performance** | [performance-guide.md](references/performance-guide.md) | Profiling, LOD, draw calls, mobile optimization, memory |
| **Calibration Scripts** | [scripts/README.md](scripts/README.md) | GLTF calibration helper installation and usage |

---

## Philosophy: The Scene Graph Mental Model

Three.js is built on the **scene graph** -- a hierarchical tree of objects where parent transformations affect children.

**Before creating a Three.js app, ask**:
- What is the **core visual element**? (geometry, shape, model)
- What **interaction** does the user need? (none, orbit controls, custom input)
- What **performance** constraints exist? (mobile, desktop, WebGL capabilities)
- What **animation** brings it to life? (rotation, movement, transitions)

**Core principles**:

1. **Scene Graph First**: Everything added to `scene` renders. Use `Group` for hierarchical transforms.
2. **Primitives as Building Blocks**: Built-in geometries (Box, Sphere, Torus) cover 80% of simple use cases.
3. **Animation as Transformation**: Change position/rotation/scale over time using `renderer.setAnimationLoop`.
4. **Performance Through Simplicity**: Fewer objects, fewer draw calls, reusable geometries/materials.

---

## Quick Start: Essential Setup

### Minimal HTML Template (r170+)

```html
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Three.js App</title>
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body { overflow: hidden; background: #000; }
        canvas { display: block; }
    </style>
</head>
<body>
    <script type="importmap">
    {
        "imports": {
            "three": "https://unpkg.com/three@0.170.0/build/three.module.js",
            "three/addons/": "https://unpkg.com/three@0.170.0/examples/jsm/"
        }
    }
    </script>

    <script type="module">
        import * as THREE from 'three';

        // Scene setup
        const scene = new THREE.Scene();
        const camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000);
        const renderer = new THREE.WebGLRenderer({ antialias: true });

        renderer.setSize(window.innerWidth, window.innerHeight);
        renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
        document.body.appendChild(renderer.domElement);

        // Your 3D content here
        // ...

        camera.position.z = 5;

        // Animation loop
        renderer.setAnimationLoop((time) => {
            renderer.render(scene, camera);
        });

        // Handle resize
        window.addEventListener('resize', () => {
            camera.aspect = window.innerWidth / window.innerHeight;
            camera.updateProjectionMatrix();
            renderer.setSize(window.innerWidth, window.innerHeight);
        });
    </script>
</body>
</html>
```

> **Note**: Import maps with `three/addons/` paths are the standard for r160+. Use `three@0.170.0` or later. WebGPURenderer is available as a modern alternative but WebGLRenderer remains the default for broad compatibility.

---

## Geometries

Built-in primitives cover most simple app needs. Use `BufferGeometry` only for custom shapes.

**Common primitives**:
- `BoxGeometry(width, height, depth)` - cubes, boxes
- `SphereGeometry(radius, widthSegments, heightSegments)` - balls, planets
- `CylinderGeometry(radiusTop, radiusBottom, height)` - tubes, cylinders
- `TorusGeometry(radius, tube)` - donuts, rings
- `PlaneGeometry(width, height)` - floors, walls, backgrounds
- `ConeGeometry(radius, height)` - spikes, cones
- `IcosahedronGeometry(radius, detail)` - low-poly spheres (detail=0)

**Usage**:
```javascript
const geometry = new THREE.BoxGeometry(1, 1, 1);
const material = new THREE.MeshStandardMaterial({ color: 0x44aa88 });
const mesh = new THREE.Mesh(geometry, material);
scene.add(mesh);
```

---

## Materials

Choose material based on lighting needs and visual style.

**Material selection guide**:
- `MeshBasicMaterial` - No lighting, flat colors. Use for: UI, wireframes, unlit effects
- `MeshStandardMaterial` - PBR lighting. Default for realistic surfaces
- `MeshPhysicalMaterial` - Advanced PBR with clearcoat, transmission. Glass, water
- `MeshNormalMaterial` - Debug, rainbow colors based on normals
- `MeshPhongMaterial` - Legacy, shininess control. Faster than Standard

**Common material properties**:
```javascript
{
    color: 0x44aa88,           // Hex color
    roughness: 0.5,            // 0=glossy, 1=matte (Standard/Physical)
    metalness: 0.0,            // 0=non-metal, 1=metal (Standard/Physical)
    emissive: 0x000000,        // Self-illumination color
    wireframe: false,          // Show edges only
    transparent: false,        // Enable transparency
    opacity: 1.0,              // 0=invisible, 1=opaque (needs transparent:true)
    side: THREE.FrontSide      // FrontSide, BackSide, DoubleSide
}
```

---

## Lighting

No light = black screen (except BasicMaterial/NormalMaterial).

**Light types**:
- `AmbientLight(intensity)` - Base illumination everywhere. Use 0.3-0.5
- `DirectionalLight(color, intensity)` - Sun-like, parallel rays. Cast shadows
- `PointLight(color, intensity, distance)` - Light bulb, emits in all directions
- `SpotLight(color, intensity, angle, penumbra)` - Flashlight, cone of light

**Typical lighting setup**:
```javascript
const ambientLight = new THREE.AmbientLight(0xffffff, 0.4);
scene.add(ambientLight);

const mainLight = new THREE.DirectionalLight(0xffffff, 1);
mainLight.position.set(5, 10, 7);
scene.add(mainLight);

const fillLight = new THREE.DirectionalLight(0x88ccff, 0.5);
fillLight.position.set(-5, 0, -5);
scene.add(fillLight);
```

**Shadows** (advanced, use when needed):
```javascript
renderer.shadowMap.enabled = true;
renderer.shadowMap.type = THREE.PCFSoftShadowMap;

mainLight.castShadow = true;
mainLight.shadow.mapSize.width = 2048;
mainLight.shadow.mapSize.height = 2048;

mesh.castShadow = true;
mesh.receiveShadow = true;
```

---

## Animation

Transform objects over time using the animation loop.

**Animation patterns**:

1. **Continuous rotation**:
```javascript
renderer.setAnimationLoop((time) => {
    mesh.rotation.x = time * 0.001;
    mesh.rotation.y = time * 0.0005;
    renderer.render(scene, camera);
});
```

2. **Wave/bobbing motion**:
```javascript
renderer.setAnimationLoop((time) => {
    mesh.position.y = Math.sin(time * 0.002) * 0.5;
    renderer.render(scene, camera);
});
```

3. **Mouse interaction**:
```javascript
const mouse = new THREE.Vector2();

window.addEventListener('mousemove', (event) => {
    mouse.x = (event.clientX / window.innerWidth) * 2 - 1;
    mouse.y = -(event.clientY / window.innerHeight) * 2 + 1;
});

renderer.setAnimationLoop(() => {
    mesh.rotation.x = mouse.y * 0.5;
    mesh.rotation.y = mouse.x * 0.5;
    renderer.render(scene, camera);
});
```

---

## Camera Controls

Import OrbitControls for interactive camera movement:

```javascript
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

// ... scene setup ...

const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true;
controls.dampingFactor = 0.05;

renderer.setAnimationLoop(() => {
    controls.update();
    renderer.render(scene, camera);
});
```

---

## Game Architecture (Overview)

For game development, Three.js provides the rendering layer. You build game systems on top:

1. **Game Loop** - State machine + delta-time updates. See [game-loop-and-state.md](references/game-loop-and-state.md)
2. **Input** - Keyboard/gamepad/touch abstracted into actions. See [input-handling.md](references/input-handling.md)
3. **Animation** - GLTF crossfading with guards. See [animation-guide.md](references/animation-guide.md)
4. **Collision** - AABB/sphere/raycaster or physics engine. See [collision-and-physics.md](references/collision-and-physics.md)
5. **Audio** - Positional 3D sound + music. See [audio-guide.md](references/audio-guide.md)
6. **UI** - HTML overlay for HUD/menus. See [ui-systems.md](references/ui-systems.md)
7. **Scenes** - Level loading/unloading with proper dispose. See [scene-management.md](references/scene-management.md)
8. **Performance** - Profile first, optimize second. See [performance-guide.md](references/performance-guide.md)

**Architecture pattern**: Keep rendering separate from game logic. The game loop updates state, then rendering reads state to draw.

---

## Common Scene Patterns

### Rotating Cube (Hello World)
```javascript
const geometry = new THREE.BoxGeometry(1, 1, 1);
const material = new THREE.MeshStandardMaterial({ color: 0x00ff88 });
const cube = new THREE.Mesh(geometry, material);
scene.add(cube);

renderer.setAnimationLoop((time) => {
    cube.rotation.x = time * 0.001;
    cube.rotation.y = time * 0.001;
    renderer.render(scene, camera);
});
```

### Floating Particle Field
```javascript
const particleCount = 1000;
const geometry = new THREE.BufferGeometry();
const positions = new Float32Array(particleCount * 3);

for (let i = 0; i < particleCount * 3; i += 3) {
    positions[i] = (Math.random() - 0.5) * 50;
    positions[i + 1] = (Math.random() - 0.5) * 50;
    positions[i + 2] = (Math.random() - 0.5) * 50;
}

geometry.setAttribute('position', new THREE.BufferAttribute(positions, 3));
const material = new THREE.PointsMaterial({ color: 0xffffff, size: 0.1 });
const particles = new THREE.Points(geometry, material);
scene.add(particles);
```

### Animated Background with Foreground Object
```javascript
const gridHelper = new THREE.GridHelper(50, 50, 0x444444, 0x222222);
scene.add(gridHelper);

const mainGeometry = new THREE.IcosahedronGeometry(1, 0);
const mainMaterial = new THREE.MeshStandardMaterial({
    color: 0xff6600,
    flatShading: true
});
const mainMesh = new THREE.Mesh(mainGeometry, mainMaterial);
scene.add(mainMesh);
```

---

## Colors

Three.js uses hexadecimal color format: `0xRRGGBB`

Common hex colors:
- Black: `0x000000`, White: `0xffffff`
- Red: `0xff0000`, Green: `0x00ff00`, Blue: `0x0000ff`
- Cyan: `0x00ffff`, Magenta: `0xff00ff`, Yellow: `0xffff00`
- Orange: `0xff8800`, Purple: `0x8800ff`, Pink: `0xff0088`

---

## Anti-Patterns to Avoid

### Basic Setup Mistakes

- **Not importing OrbitControls from correct path** -- Use `import { OrbitControls } from 'three/addons/controls/OrbitControls.js'`
- **Forgetting to add object to scene** -- Always call `scene.add(object)` after creating meshes/lights
- **Using old `requestAnimationFrame` pattern** -- Use `renderer.setAnimationLoop((time) => { ... })`

### Performance Issues

- **Creating new geometries in animation loop** -- Create once, reuse. Transform position/rotation/scale only
- **Using too many segments on primitives** -- `SphereGeometry(1, 32, 16)` not `SphereGeometry(1, 128, 64)`
- **Not setting pixelRatio cap** -- `Math.min(window.devicePixelRatio, 2)`

### Code Organization

- **Everything in one giant function** -- Separate: `createScene()`, `createLights()`, `createMeshes()`
- **Hardcoding all values** -- Define constants: `const CONFIG = { color: 0x00ff88, speed: 0.001 }`

---

## Variation Guidance

**IMPORTANT**: Each Three.js app should feel unique and context-appropriate.

**Vary by scenario**:
- **Portfolio/showcase**: Elegant, smooth animations, muted colors
- **Game/interactive**: Bright colors, snappy controls, particle effects
- **Data visualization**: Clean lines, grid helpers, clear labels
- **Background effect**: Subtle, slow movement, dark/gradient backgrounds
- **Product viewer**: Realistic lighting, PBR materials, smooth orbit

**Vary visual elements**:
- **Geometry choice**: Not everything needs to be a cube. Explore spheres, tori, icosahedra
- **Material style**: Mix flat shaded, glossy, metallic, wireframe
- **Color palettes**: Use complementary, analogous, or monochromatic schemes
- **Animation style**: Rotation, oscillation, wave motion, mouse tracking

**Avoid converging on**:
- Default green cube as first example every time
- Same camera angle (front-facing, z=5)
- Identical lighting setup (always directional light at 1,1,1)

---

## Remember

**Three.js is a tool for interactive 3D on the web.**

Effective Three.js apps:
- Start with the scene graph mental model
- Use primitives as building blocks
- Keep animations simple and performant
- Vary visual style based on purpose
- Import from modern ES module paths (`three/addons/`)

**Modern Three.js (r170+) uses ES modules with import maps.** CommonJS patterns and global `THREE` variable are legacy.

**Claude is capable of creating elegant, performant 3D web experiences and games. These patterns guide the way -- they don't limit the result.**

For specific topics, see the **Reference Files** table at the top of this document.
