# Advanced Rendering

Post-processing, custom shaders, environment maps, instancing, BatchedMesh, and other advanced Three.js rendering techniques.

---

## Post-Processing (Bloom, Depth of Field)

```javascript
import * as THREE from 'three';
import { EffectComposer } from 'three/addons/postprocessing/EffectComposer.js';
import { RenderPass } from 'three/addons/postprocessing/RenderPass.js';
import { UnrealBloomPass } from 'three/addons/postprocessing/UnrealBloomPass.js';

const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setSize(window.innerWidth, window.innerHeight);
renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
renderer.toneMapping = THREE.ReinhardToneMapping;

const renderScene = new RenderPass(scene, camera);

const bloomPass = new UnrealBloomPass(
    new THREE.Vector2(window.innerWidth, window.innerHeight),
    1.5,  // strength
    0.4,  // radius
    0.85  // threshold
);

const composer = new EffectComposer(renderer);
composer.addPass(renderScene);
composer.addPass(bloomPass);

renderer.setAnimationLoop(() => {
    composer.render();
});
```

---

## Custom Shaders (ShaderMaterial)

```javascript
const vertexShader = `
    varying vec2 vUv;
    void main() {
        vUv = uv;
        gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
    }
`;

const fragmentShader = `
    uniform float time;
    varying vec2 vUv;
    void main() {
        vec3 color = 0.5 + 0.5 * cos(time + vUv.xyx + vec3(0, 2, 4));
        gl_FragColor = vec4(color, 1.0);
    }
`;

const material = new THREE.ShaderMaterial({
    vertexShader,
    fragmentShader,
    uniforms: {
        time: { value: 0 }
    }
});

renderer.setAnimationLoop((time) => {
    material.uniforms.time.value = time * 0.001;
    renderer.render(scene, camera);
});
```

---

## Text and Sprites

Canvas-based text for 3D space labels:

```javascript
function createTextSprite(message, scale = 1) {
    const canvas = document.createElement('canvas');
    const context = canvas.getContext('2d');
    canvas.width = 256;
    canvas.height = 64;

    context.fillStyle = 'rgba(0, 0, 0, 0)';
    context.fillRect(0, 0, canvas.width, canvas.height);
    context.font = 'Bold 24px Arial';
    context.fillStyle = 'white';
    context.textAlign = 'center';
    context.fillText(message, canvas.width / 2, canvas.height / 2);

    const texture = new THREE.CanvasTexture(canvas);
    const material = new THREE.SpriteMaterial({ map: texture });
    const sprite = new THREE.Sprite(material);
    sprite.scale.set(scale * 4, scale, 1);
    return sprite;
}

const label = createTextSprite('Hello Three.js!', 1);
label.position.set(0, 2, 0);
scene.add(label);
```

---

## Raycasting (Mouse Picking)

```javascript
const raycaster = new THREE.Raycaster();
const mouse = new THREE.Vector2();

window.addEventListener('click', (event) => {
    mouse.x = (event.clientX / window.innerWidth) * 2 - 1;
    mouse.y = -(event.clientY / window.innerHeight) * 2 + 1;

    raycaster.setFromCamera(mouse, camera);
    const intersects = raycaster.intersectObjects(scene.children);

    if (intersects.length > 0) {
        const object = intersects[0].object;
        object.material.color.setHex(Math.random() * 0xffffff);
    }
});
```

---

## Environment Maps (Reflections)

```javascript
import { RGBELoader } from 'three/addons/loaders/RGBELoader.js';

const rgbeLoader = new RGBELoader();
rgbeLoader.load('path/to/environment.hdr', (texture) => {
    texture.mapping = THREE.EquirectangularReflectionMapping;
    scene.environment = texture;
    scene.background = texture;
});

const material = new THREE.MeshStandardMaterial({
    color: 0x444444,
    metalness: 1,
    roughness: 0.1
});
```

---

## InstancedMesh (Many Similar Objects)

For rendering thousands of identical objects with one draw call:

```javascript
const count = 1000;
const geometry = new THREE.BoxGeometry(0.2, 0.2, 0.2);
const material = new THREE.MeshStandardMaterial({ color: 0x44aa88 });
const mesh = new THREE.InstancedMesh(geometry, material, count);

const dummy = new THREE.Object3D();
for (let i = 0; i < count; i++) {
    dummy.position.set(
        (Math.random() - 0.5) * 20,
        (Math.random() - 0.5) * 20,
        (Math.random() - 0.5) * 20
    );
    dummy.rotation.set(Math.random() * Math.PI, Math.random() * Math.PI, 0);
    dummy.updateMatrix();
    mesh.setMatrixAt(i, dummy.matrix);
}

scene.add(mesh);
```

---

## BatchedMesh (r170+)

`BatchedMesh` is a newer alternative to `InstancedMesh` that supports **multiple different geometries** in a single draw call. Use when you have varied objects (trees, rocks, buildings) that share a material.

```javascript
import * as THREE from 'three';

// Create a BatchedMesh with capacity estimates
const batchedMesh = new THREE.BatchedMesh(
    100,     // max geometry count
    5000,    // max vertex count
    10000,   // max index count
    new THREE.MeshStandardMaterial({ color: 0x44aa88 })
);

// Add different geometries
const boxGeoId = batchedMesh.addGeometry(new THREE.BoxGeometry(1, 1, 1));
const sphereGeoId = batchedMesh.addGeometry(new THREE.SphereGeometry(0.5, 16, 8));
const coneGeoId = batchedMesh.addGeometry(new THREE.ConeGeometry(0.5, 1, 8));

// Add instances of each geometry
const matrix = new THREE.Matrix4();
for (let i = 0; i < 30; i++) {
    matrix.makeTranslation(
        (Math.random() - 0.5) * 20,
        (Math.random() - 0.5) * 20,
        (Math.random() - 0.5) * 20
    );

    // Randomly pick a geometry
    const geoId = [boxGeoId, sphereGeoId, coneGeoId][Math.floor(Math.random() * 3)];
    batchedMesh.addInstance(geoId, matrix);
}

scene.add(batchedMesh);
```

**When to use which**:
- `InstancedMesh`: All objects use the **same geometry** (forest of identical trees)
- `BatchedMesh`: Objects use **different geometries** but the same material (mixed props)
- Regular `Mesh`: Unique objects or very few instances

---

## Physics Integration (Cannon-es)

```javascript
import * as CANNON from 'cannon-es';

const world = new CANNON.World();
world.gravity.set(0, -9.82, 0);

// Sync mesh with physics body
const body = new CANNON.Body({
    mass: 1,
    shape: new CANNON.Sphere(0.5),
    position: new CANNON.Vec3(0, 5, 0)
});
world.addBody(body);

// Ground
const groundBody = new CANNON.Body({
    type: CANNON.Body.STATIC,
    shape: new CANNON.Plane()
});
groundBody.quaternion.setFromEuler(-Math.PI / 2, 0, 0);
world.addBody(groundBody);

const timeStep = 1 / 60;
renderer.setAnimationLoop(() => {
    world.step(timeStep);
    mesh.position.copy(body.position);
    mesh.quaternion.copy(body.quaternion);
    renderer.render(scene, camera);
});
```

---

## Key Module Import Paths (r170+)

```javascript
// Core
import * as THREE from 'three';

// Addons (three/addons/ in npm, examples/jsm/ in CDN)
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { GLTFLoader } from 'three/addons/loaders/GLTFLoader.js';
import { RGBELoader } from 'three/addons/loaders/RGBELoader.js';
import { EffectComposer } from 'three/addons/postprocessing/EffectComposer.js';
import { UnrealBloomPass } from 'three/addons/postprocessing/UnrealBloomPass.js';
import { RenderPass } from 'three/addons/postprocessing/RenderPass.js';
```

---

## npm Installation

```bash
npm install three
```

```javascript
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
```

---

## TypeScript Support

```typescript
import * as THREE from 'three';

const scene: THREE.Scene = new THREE.Scene();
const geometry: THREE.BoxGeometry = new THREE.BoxGeometry(1, 1, 1);
const material: THREE.MeshStandardMaterial = new THREE.MeshStandardMaterial({
    color: 0x44aa88
});
const cube: THREE.Mesh = new THREE.Mesh(geometry, material);
scene.add(cube);
```

---

## Debug Helpers

```javascript
// Grid helper
const gridHelper = new THREE.GridHelper(10, 10);
scene.add(gridHelper);

// Axes helper (RGB = XYZ)
const axesHelper = new THREE.AxesHelper(5);
scene.add(axesHelper);

// Stats.js for performance monitoring
import Stats from 'three/addons/libs/stats.module.js';
const stats = new Stats();
document.body.appendChild(stats.dom);

renderer.setAnimationLoop(() => {
    stats.begin();
    renderer.render(scene, camera);
    stats.end();
});
```
