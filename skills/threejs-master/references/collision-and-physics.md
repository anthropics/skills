# Collision & Physics

Collision detection patterns and physics engine integration for Three.js games.

---

## AABB Collision (Box3 Intersection)

The simplest collision check -- axis-aligned bounding boxes:

```javascript
const playerBox = new THREE.Box3();
const obstacleBox = new THREE.Box3();

function checkAABBCollision(objA, objB) {
    playerBox.setFromObject(objA);
    obstacleBox.setFromObject(objB);
    return playerBox.intersectsBox(obstacleBox);
}

// Usage in game loop
function checkCollisions() {
    for (const obstacle of obstacles) {
        if (checkAABBCollision(player, obstacle)) {
            onPlayerHit(obstacle);
        }
    }
}
```

**Optimization**: Pre-compute boxes, only update when objects move:

```javascript
// Attach box to object userData
function initCollider(obj, padding = 0) {
    const box = new THREE.Box3().setFromObject(obj);
    if (padding) {
        box.expandByScalar(padding);
    }
    obj.userData.collider = box;
}

function updateCollider(obj) {
    obj.userData.collider.setFromObject(obj);
}
```

---

## Sphere Collision (Distance-Based)

Faster than AABB for round objects. Good for characters, projectiles, pickups:

```javascript
function checkSphereCollision(posA, radiusA, posB, radiusB) {
    const distance = posA.distanceTo(posB);
    return distance < (radiusA + radiusB);
}

// Usage
const playerRadius = 0.5;
const coinRadius = 0.3;

function checkCoinPickups() {
    for (let i = coins.length - 1; i >= 0; i--) {
        if (checkSphereCollision(
            player.position, playerRadius,
            coins[i].position, coinRadius
        )) {
            collectCoin(coins[i]);
            coins.splice(i, 1);
        }
    }
}
```

---

## Raycaster for Ground Detection

Cast a ray downward to find the ground surface:

```javascript
const downRay = new THREE.Raycaster();
const downDirection = new THREE.Vector3(0, -1, 0);

function getGroundHeight(position, groundMeshes) {
    // Cast from above the position
    const origin = position.clone();
    origin.y += 10;

    downRay.set(origin, downDirection);
    const hits = downRay.intersectObjects(groundMeshes);

    if (hits.length > 0) {
        return hits[0].point.y;
    }

    return 0; // Default ground level
}

// Usage: keep player on terrain
function updatePlayerGround() {
    const groundY = getGroundHeight(player.position, [terrain]);
    player.position.y = groundY + playerHeight / 2;
}
```

---

## Raycaster for Mouse Picking

```javascript
const raycaster = new THREE.Raycaster();
const mouse = new THREE.Vector2();

function getClickedObject(event, camera, targets) {
    mouse.x = (event.clientX / window.innerWidth) * 2 - 1;
    mouse.y = -(event.clientY / window.innerHeight) * 2 + 1;

    raycaster.setFromCamera(mouse, camera);
    const hits = raycaster.intersectObjects(targets, true); // true = recursive

    return hits.length > 0 ? hits[0] : null;
}

// Usage
canvas.addEventListener('click', (event) => {
    const hit = getClickedObject(event, camera, clickableObjects);
    if (hit) {
        console.log('Clicked:', hit.object.name, 'at', hit.point);
    }
});
```

---

## Trigger Zones (Enter/Exit Callbacks)

Invisible volumes that fire events when objects enter or leave:

```javascript
class TriggerZone {
    constructor(position, size, onEnter, onExit) {
        this.box = new THREE.Box3(
            new THREE.Vector3().copy(position).sub(size.clone().multiplyScalar(0.5)),
            new THREE.Vector3().copy(position).add(size.clone().multiplyScalar(0.5))
        );
        this.onEnter = onEnter;
        this.onExit = onExit;
        this.inside = new Set();
    }

    check(obj) {
        const objBox = new THREE.Box3().setFromObject(obj);
        const overlaps = this.box.intersectsBox(objBox);
        const id = obj.uuid;

        if (overlaps && !this.inside.has(id)) {
            this.inside.add(id);
            this.onEnter?.(obj);
        } else if (!overlaps && this.inside.has(id)) {
            this.inside.delete(id);
            this.onExit?.(obj);
        }
    }
}

// Usage
const checkpoint = new TriggerZone(
    new THREE.Vector3(10, 1, 0),
    new THREE.Vector3(2, 3, 2),
    (obj) => console.log('Entered checkpoint!'),
    (obj) => console.log('Left checkpoint')
);

// In game loop
checkpoint.check(player);
```

---

## Collision Layers / Groups

Filter which objects can collide with each other:

```javascript
const CollisionLayer = {
    PLAYER: 1,
    ENEMY: 2,
    PROJECTILE: 4,
    PICKUP: 8,
    ENVIRONMENT: 16
};

// Define what each layer collides with
const CollisionMask = {
    PLAYER: CollisionLayer.ENEMY | CollisionLayer.PICKUP | CollisionLayer.ENVIRONMENT,
    ENEMY: CollisionLayer.PLAYER | CollisionLayer.PROJECTILE | CollisionLayer.ENVIRONMENT,
    PROJECTILE: CollisionLayer.ENEMY | CollisionLayer.ENVIRONMENT,
    PICKUP: CollisionLayer.PLAYER
};

function canCollide(layerA, layerB) {
    // Bitwise check: A's layer is in B's mask, or B's layer is in A's mask
    return (layerA & CollisionMask[layerB]) !== 0 ||
           (layerB & CollisionMask[layerA]) !== 0;
}
```

---

## Spatial Hashing (Broad Phase)

For many objects, avoid O(n^2) collision checks:

```javascript
class SpatialHash {
    constructor(cellSize = 4) {
        this.cellSize = cellSize;
        this.cells = new Map();
    }

    _key(x, z) {
        const cx = Math.floor(x / this.cellSize);
        const cz = Math.floor(z / this.cellSize);
        return `${cx},${cz}`;
    }

    clear() {
        this.cells.clear();
    }

    insert(obj) {
        const key = this._key(obj.position.x, obj.position.z);
        if (!this.cells.has(key)) {
            this.cells.set(key, []);
        }
        this.cells.get(key).push(obj);
    }

    getNearby(obj) {
        const cx = Math.floor(obj.position.x / this.cellSize);
        const cz = Math.floor(obj.position.z / this.cellSize);
        const nearby = [];

        // Check 3x3 grid of cells around object
        for (let dx = -1; dx <= 1; dx++) {
            for (let dz = -1; dz <= 1; dz++) {
                const key = `${cx + dx},${cz + dz}`;
                const cell = this.cells.get(key);
                if (cell) nearby.push(...cell);
            }
        }

        return nearby;
    }
}

// Usage in game loop
const spatialHash = new SpatialHash(4);

function checkCollisions() {
    spatialHash.clear();

    // Insert all collidable objects
    for (const obj of allCollidables) {
        spatialHash.insert(obj);
    }

    // Only check nearby objects
    const nearby = spatialHash.getNearby(player);
    for (const obj of nearby) {
        if (obj !== player && checkSphereCollision(player, obj)) {
            handleCollision(player, obj);
        }
    }
}
```

---

## Physics Engine Integration

### Cannon-es (Lightweight)

```bash
npm install cannon-es
# or CDN: https://unpkg.com/cannon-es@0.20.0/dist/cannon-es.js
```

```javascript
import * as CANNON from 'cannon-es';

const world = new CANNON.World({ gravity: new CANNON.Vec3(0, -9.82, 0) });

// Create physics body for each mesh
function addPhysicsBody(mesh, options = {}) {
    const { mass = 1, shape } = options;

    const body = new CANNON.Body({ mass, shape });
    body.position.copy(mesh.position);
    body.quaternion.copy(mesh.quaternion);
    world.addBody(body);

    mesh.userData.physicsBody = body;
    return body;
}

// Sync in animation loop
function syncPhysics() {
    world.step(1 / 60);

    for (const mesh of physicsMeshes) {
        const body = mesh.userData.physicsBody;
        mesh.position.copy(body.position);
        mesh.quaternion.copy(body.quaternion);
    }
}
```

### Rapier3D (High Performance, WASM)

```bash
npm install @dimforge/rapier3d
```

```javascript
import RAPIER from '@dimforge/rapier3d';

await RAPIER.init();

const gravity = { x: 0.0, y: -9.81, z: 0.0 };
const world = new RAPIER.World(gravity);

// Rigid body + collider
const bodyDesc = RAPIER.RigidBodyDesc.dynamic().setTranslation(0, 5, 0);
const body = world.createRigidBody(bodyDesc);

const colliderDesc = RAPIER.ColliderDesc.ball(0.5);
world.createCollider(colliderDesc, body);

// Step + sync
function update() {
    world.step();

    const pos = body.translation();
    const rot = body.rotation();
    mesh.position.set(pos.x, pos.y, pos.z);
    mesh.quaternion.set(rot.x, rot.y, rot.z, rot.w);
}
```

**When to use which**:
- **No engine** (AABB/sphere): Simple games, 2.5D, few colliders
- **Cannon-es**: Medium complexity, easy API, good enough for most games
- **Rapier3D**: High performance, deterministic, complex physics (vehicles, ragdolls)
