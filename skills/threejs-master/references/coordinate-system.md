# Three.js Coordinate System (CRITICAL)

Understanding Three.js's right-handed coordinate system is **essential** to avoid inverted movement, wrong-facing models, and broken collision detection.

---

## The Axes

```
      +Y (up)
       |
       |
       |_______ +X (right)
      /
     /
    +Z (toward camera/viewer)
```

**Memory aid**: Point your thumb (+X), index finger (+Y), middle finger (+Z) - that's right-handed coordinates.

| Axis | Direction | Common Usage |
|------|-----------|--------------|
| +X   | Right     | Strafe right, spawn right |
| -X   | Left      | Strafe left, spawn left |
| +Y   | Up        | Jump, height |
| -Y   | Down      | Fall, gravity |
| +Z   | Toward camera | Approach viewer, "forward" in many setups |
| -Z   | Away from camera | Retreat, **GLTF models face -Z by default** |

---

## GLTF Model Default Orientation

**CRITICAL**: GLTF models exported from Blender/Maya face **-Z** (into the screen) by default.

```javascript
// GLTF model faces -Z. To face +Z (toward camera):
model.rotation.y = Math.PI;  // 180 degree rotation

// To face +X (right):
model.rotation.y = -Math.PI / 2;  // -90 degrees

// To face -X (left):
model.rotation.y = Math.PI / 2;   // +90 degrees
```

---

## Camera-Relative Movement (CRITICAL for Games)

**PROBLEM**: When camera is at an angle (e.g., isometric view), raw WASD input moves wrong!

```javascript
// WRONG - Input is world-axis relative, not camera-relative
if (keyW) player.position.z -= speed;  // Moves toward -Z, not "forward" from player's view
if (keyD) player.position.x += speed;  // Moves +X, not "right" from camera's view

// CORRECT - Calculate camera-relative directions
function updateMovement(deltaTime) {
    // Get camera's forward direction, projected onto ground (XZ plane)
    const forward = new THREE.Vector3();
    camera.getWorldDirection(forward);
    forward.y = 0;
    forward.normalize();

    // Calculate right vector (cross product of forward and world up)
    const right = new THREE.Vector3();
    right.crossVectors(forward, new THREE.Vector3(0, 1, 0)).normalize();

    // Apply input relative to camera orientation
    const velocity = new THREE.Vector3();
    if (inputState.up) velocity.add(forward);
    if (inputState.down) velocity.sub(forward);
    if (inputState.right) velocity.add(right);
    if (inputState.left) velocity.sub(right);

    if (velocity.length() > 0) {
        velocity.normalize().multiplyScalar(speed * deltaTime);
        player.position.add(velocity);

        // Face movement direction
        player.rotation.y = Math.atan2(velocity.x, velocity.z);
    }
}
```

**Why this matters**: With camera at `(8, 11, -6)` looking at `(0, 1, 3)`:
- "Forward" visually is NOT `-Z`, it's roughly `+Z`
- "Right" visually is NOT `+X`, it's roughly `-X + Z`
- Raw axis input feels completely inverted to players

---

## Object3D Forward Convention

In Three.js, an `Object3D`'s forward direction is its **local `-Z` axis**.

```javascript
// Get the world-space direction an object is "facing"
const worldForward = new THREE.Vector3();
object.getWorldDirection(worldForward);
// Returns the object's local -Z axis in world coordinates
```

This is important for:
- Character facing direction
- Projectile launch direction
- Camera orientation
- AI steering behaviors

---

## Common Rotation Cheat Sheet

| Desired Facing | rotation.y Value | Notes |
|----------------|------------------|-------|
| -Z (default GLTF) | `0` | Into screen |
| +Z (toward camera) | `Math.PI` | 180 degrees |
| +X (right) | `-Math.PI / 2` | -90 degrees |
| -X (left) | `Math.PI / 2` | +90 degrees |
| Arbitrary angle | `Math.atan2(dirX, dirZ)` | Face any XZ direction |
