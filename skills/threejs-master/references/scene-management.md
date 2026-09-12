# Scene Management

Level loading/unloading, transitions, asset preloading, and dispose patterns for Three.js games.

---

## The dispose() Contract

Three.js does NOT automatically garbage collect GPU resources. You must manually dispose:

- **Geometries**: `geometry.dispose()`
- **Materials**: `material.dispose()`
- **Textures**: `texture.dispose()`
- **Render targets**: `renderTarget.dispose()`

```javascript
// Dispose a single mesh completely
function disposeMesh(mesh) {
    if (mesh.geometry) mesh.geometry.dispose();

    if (mesh.material) {
        // Material can be an array
        const materials = Array.isArray(mesh.material) ? mesh.material : [mesh.material];

        for (const mat of materials) {
            // Dispose all texture maps
            for (const key of Object.keys(mat)) {
                const value = mat[key];
                if (value && value.isTexture) {
                    value.dispose();
                }
            }
            mat.dispose();
        }
    }
}

// Dispose an entire scene tree recursively
function disposeTree(obj) {
    while (obj.children.length > 0) {
        disposeTree(obj.children[0]);
        obj.remove(obj.children[0]);
    }

    if (obj.isMesh) {
        disposeMesh(obj);
    }
}
```

---

## Level Loading / Unloading

```javascript
class LevelManager {
    constructor(scene) {
        this.scene = scene;
        this.currentLevel = null;
        this.levelRoot = new THREE.Group();
        this.scene.add(this.levelRoot);
        this.mixers = [];
    }

    async load(levelData) {
        // Unload previous level first
        this.unload();

        // Load new level assets
        const loader = new GLTFLoader();

        for (const asset of levelData.assets) {
            const gltf = await new Promise((resolve, reject) => {
                loader.load(asset.path, resolve, undefined, reject);
            });

            const model = gltf.scene;
            model.position.copy(asset.position || new THREE.Vector3());
            model.rotation.set(...(asset.rotation || [0, 0, 0]));

            if (asset.scale) model.scale.setScalar(asset.scale);

            // Setup animations
            if (gltf.animations.length > 0) {
                const mixer = new THREE.AnimationMixer(model);
                mixer.clipAction(gltf.animations[0]).play();
                this.mixers.push(mixer);
            }

            this.levelRoot.add(model);
        }

        this.currentLevel = levelData.name;
    }

    unload() {
        // Stop all animations
        for (const mixer of this.mixers) {
            mixer.stopAllAction();
        }
        this.mixers = [];

        // Dispose all geometry/material/textures
        disposeTree(this.levelRoot);

        this.currentLevel = null;
    }

    update(dt) {
        for (const mixer of this.mixers) {
            mixer.update(dt);
        }
    }
}
```

---

## Scene Transitions

### Fade to Black

```javascript
const fadeOverlay = document.getElementById('fade-overlay');
// HTML: <div id="fade-overlay" style="position:absolute; top:0; left:0; width:100%; height:100%; background:black; opacity:0; pointer-events:none; transition:opacity 0.5s;"></div>

async function fadeTransition(loadFn) {
    // Fade to black
    fadeOverlay.style.opacity = '1';
    fadeOverlay.style.pointerEvents = 'all';

    await wait(500);

    // Load new content while screen is black
    await loadFn();

    await wait(200); // Brief hold

    // Fade back in
    fadeOverlay.style.opacity = '0';
    fadeOverlay.style.pointerEvents = 'none';
}

function wait(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

// Usage
await fadeTransition(async () => {
    levelManager.unload();
    await levelManager.load(level2Data);
});
```

### Crossfade Between Scenes

For smoother transitions, render both scenes to textures and blend:

```javascript
async function crossfadeTransition(loadFn, duration = 1) {
    // Capture current frame as texture
    const renderTarget = new THREE.WebGLRenderTarget(
        window.innerWidth, window.innerHeight
    );
    renderer.setRenderTarget(renderTarget);
    renderer.render(scene, camera);
    renderer.setRenderTarget(null);

    // Create fullscreen quad with the captured texture
    const quadGeometry = new THREE.PlaneGeometry(2, 2);
    const quadMaterial = new THREE.MeshBasicMaterial({
        map: renderTarget.texture,
        transparent: true,
        depthTest: false
    });
    const quad = new THREE.Mesh(quadGeometry, quadMaterial);

    // Load new scene while showing the frozen frame
    await loadFn();

    // Render the quad over the new scene, fading out
    const orthoCamera = new THREE.OrthographicCamera(-1, 1, 1, -1, 0, 1);
    const orthoScene = new THREE.Scene();
    orthoScene.add(quad);

    let elapsed = 0;
    const fadeOut = () => {
        elapsed += 1 / 60; // Approximate per-frame
        quadMaterial.opacity = 1 - (elapsed / duration);

        if (quadMaterial.opacity > 0) {
            renderer.render(scene, camera);
            renderer.autoClear = false;
            renderer.render(orthoScene, orthoCamera);
            renderer.autoClear = true;
            requestAnimationFrame(fadeOut);
        } else {
            // Cleanup
            quadGeometry.dispose();
            quadMaterial.dispose();
            renderTarget.dispose();
        }
    };

    fadeOut();
}
```

---

## Asset Manifest & Preloader

```javascript
const ASSET_MANIFEST = {
    models: [
        { name: 'player', path: 'models/player.glb', priority: 1 },
        { name: 'enemy_skeleton', path: 'models/skeleton.glb', priority: 1 },
        { name: 'tree_pine', path: 'models/tree.glb', priority: 2 },
        { name: 'rock_large', path: 'models/rock.glb', priority: 2 }
    ],
    textures: [
        { name: 'ground', path: 'textures/ground.jpg' },
        { name: 'skybox', path: 'textures/sky.hdr' }
    ],
    audio: [
        { name: 'bgm', path: 'audio/music.mp3' },
        { name: 'sfx_jump', path: 'audio/jump.mp3' }
    ]
};

class AssetPreloader {
    constructor() {
        this.gltfLoader = new GLTFLoader();
        this.textureLoader = new THREE.TextureLoader();
        this.audioLoader = new THREE.AudioLoader();
        this.assets = new Map();
    }

    async loadManifest(manifest, onProgress) {
        const allAssets = [
            ...manifest.models.map(a => ({ ...a, type: 'model' })),
            ...manifest.textures.map(a => ({ ...a, type: 'texture' })),
            ...manifest.audio.map(a => ({ ...a, type: 'audio' }))
        ];

        // Sort by priority (lower = load first)
        allAssets.sort((a, b) => (a.priority || 99) - (b.priority || 99));

        let loaded = 0;
        const total = allAssets.length;

        for (const asset of allAssets) {
            onProgress?.(loaded, total, asset.name);

            try {
                const result = await this._loadOne(asset);
                this.assets.set(asset.name, result);
            } catch (err) {
                console.error(`Failed to load ${asset.name}:`, err);
            }

            loaded++;
        }

        onProgress?.(total, total, 'Complete');
    }

    async _loadOne(asset) {
        switch (asset.type) {
            case 'model':
                return new Promise((resolve, reject) => {
                    this.gltfLoader.load(asset.path, resolve, undefined, reject);
                });
            case 'texture':
                return new Promise((resolve, reject) => {
                    this.textureLoader.load(asset.path, resolve, undefined, reject);
                });
            case 'audio':
                return new Promise((resolve, reject) => {
                    this.audioLoader.load(asset.path, resolve, undefined, reject);
                });
        }
    }

    get(name) {
        return this.assets.get(name);
    }
}
```

---

## Memory Cleanup Checklist

When unloading a level or removing objects, go through this checklist:

1. **Stop animations**: `mixer.stopAllAction()`, remove mixer from update list
2. **Remove from scene**: `scene.remove(object)`
3. **Dispose geometries**: `geometry.dispose()`
4. **Dispose materials**: `material.dispose()` (including all texture maps)
5. **Dispose textures**: `texture.dispose()`
6. **Remove event listeners**: `window.removeEventListener(...)` for any per-level listeners
7. **Clear references**: Set variables to `null` to allow GC
8. **Dispose render targets**: `renderTarget.dispose()` if used
9. **Dispose post-processing**: `composer.dispose()` if level-specific

```javascript
// Quick cleanup helper
function fullCleanup(object, scene) {
    // 1. Remove from scene
    scene.remove(object);

    // 2. Recursively dispose
    object.traverse((child) => {
        if (child.isMesh) {
            child.geometry?.dispose();

            const mats = Array.isArray(child.material) ? child.material : [child.material];
            for (const mat of mats) {
                for (const key of Object.keys(mat)) {
                    if (mat[key]?.isTexture) mat[key].dispose();
                }
                mat.dispose();
            }
        }
    });
}
```

---

## renderer.info for Leak Detection

```javascript
// Log GPU resource counts
function logRendererInfo() {
    const info = renderer.info;
    console.log('Renderer info:', {
        geometries: info.memory.geometries,
        textures: info.memory.textures,
        drawCalls: info.render.calls,
        triangles: info.render.triangles,
        programs: info.programs?.length
    });
}

// Call after loading/unloading to verify cleanup
// Numbers should go DOWN after unloading a level
```

---

## Anti-Patterns

- **Removing from scene without dispose** -- GPU memory leaks, eventual crash
- **Disposing shared materials** -- If material is reused, only dispose when ALL users are gone
- **Loading assets during gameplay** -- Pre-load during loading screen
- **No transition between levels** -- Jarring; always fade or crossfade
