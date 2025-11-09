# Unity Physics System

## Overview

Understanding Unity's physics system is crucial for creating responsive gameplay. This guide covers Rigidbody API changes, the critical difference between triggers and collisions, and best practices for physics-based games.

## Rigidbody API Changes (Unity 2023.1+)

### The Change

Unity 2023.1 renamed `Rigidbody.velocity` to `Rigidbody.linearVelocity` for clarity and consistency.

### Old API (Pre-2023.1)

```csharp
// Setting velocity
rb.velocity = moveDirection;

// Getting velocity
Vector3 currentVelocity = rb.velocity;

// Modifying velocity
rb.velocity += Vector3.up * jumpForce;
```

### New API (Unity 2023.1+)

```csharp
// Setting velocity
rb.linearVelocity = moveDirection;

// Getting velocity
Vector3 currentVelocity = rb.linearVelocity;

// Modifying velocity
rb.linearVelocity += Vector3.up * jumpForce;
```

### Related Changes

| Old API | New API | Notes |
|---------|---------|-------|
| `Rigidbody.velocity` | `Rigidbody.linearVelocity` | Renamed for clarity |
| `Rigidbody.angularVelocity` | `Rigidbody.angularVelocity` | Unchanged (already clear) |

### Migration

**Automatic**: Unity auto-upgrades scripts when opened in 2023.1+

**Manual**: Use Find & Replace
```csharp
// Find:    rb.velocity
// Replace: rb.linearVelocity
```

**Best Practice**: Always use `linearVelocity` for Unity 2023.1+ projects

## Triggers vs Collisions

Understanding when to use triggers vs collisions is critical for game physics.

### Collision Detection (Solid Colliders)

**Setup**:
- Collider: `IsTrigger = false`
- Requires: At least one Rigidbody on interacting objects

**Callback**:
```csharp
private void OnCollisionEnter(Collision collision)
{
    Debug.Log($"Collided with {collision.gameObject.name}");

    // Access collision information
    ContactPoint contact = collision.contacts[0];
    Vector3 normal = contact.normal;
    float impulse = collision.impulse.magnitude;
}
```

**Physics Behavior**:
- Objects physically interact
- Bouncing, pushing, momentum transfer
- Realistic physics simulation
- More expensive computationally

**When to Use**:
- Realistic physics interactions needed
- Objects should bounce or push
- Slower-moving objects
- Vehicle physics
- Ragdoll systems
- Destructible objects that react physically

### Trigger Detection (Ghost Colliders)

**Setup**:
- Collider: `IsTrigger = true`
- Requires: At least one Rigidbody on interacting objects

**Callback**:
```csharp
private void OnTriggerEnter(Collider other)
{
    Debug.Log($"Triggered by {other.gameObject.name}");

    // No collision information available
    // Just detection
}
```

**Physics Behavior**:
- No physical interaction
- Objects pass through each other
- Detection-only
- Cheaper computationally

**When to Use**:
- Fast-moving projectiles (bullets, arrows)
- Zone detection (powerups, checkpoints, sensors)
- Detection-only systems
- Performance-critical scenarios
- Guaranteed detection without tunneling

## Comparison Table

| Aspect | Collision (Solid) | Trigger (Ghost) |
|--------|------------------|-----------------|
| **Detection reliability** | Can miss fast objects (tunneling) | Always detects overlaps |
| **Physics response** | Objects bounce/react | No physical interaction |
| **Performance** | More expensive | Cheaper |
| **Information** | Contact points, impulse, normal | Basic overlap detection |
| **Use case** | Physics reactions | Detection only |
| **Rigidbody required** | Yes (at least one) | Yes (at least one) |
| **Fast objects** | Risk of tunneling | Guaranteed detection |

## Fast-Moving Objects & Tunneling

### The Tunneling Problem

Fast objects can pass through colliders between physics frames.

**Example**:
- Bullet speed: 50 units/sec
- Physics update: 0.02s (50 Hz)
- Bullet travels: 1 unit per frame
- Thin wall: 0.5 units thick
- Result: Bullet **tunnels through** wall

### Solutions

#### 1. Use Triggers (Recommended for Bullets)

```csharp
// Barrel with trigger collider
public class BarrelDestruction : MonoBehaviour
{
    [SerializeField] private LayerMask bulletLayer;

    private void OnTriggerEnter(Collider other)
    {
        if (other.gameObject.layer == bulletLayer)
        {
            Explode();
        }
    }

    private void Explode()
    {
        // Destruction logic
        Destroy(gameObject);
    }
}
```

**Setup**:
- Barrel: CapsuleCollider with `IsTrigger = true`, Rigidbody present
- Bullet: SphereCollider (solid), Rigidbody with velocity

**Benefits**:
- Guaranteed detection
- No tunneling
- Better performance
- Simple implementation

#### 2. Continuous Collision Detection

```csharp
Rigidbody rb = GetComponent<Rigidbody>();
rb.collisionDetectionMode = CollisionDetectionMode.Continuous;
// or
rb.collisionDetectionMode = CollisionDetectionMode.ContinuousDynamic;
```

**Modes**:
- **Discrete**: Default, cheapest, can tunnel
- **Continuous**: Prevents tunneling against static colliders
- **ContinuousDynamic**: Prevents tunneling against all colliders (most expensive)
- **ContinuousSpeculative**: Good balance (Unity 2022+)

**Use for**: Important physics objects that must not tunnel

#### 3. Increase Fixed Timestep

```csharp
// Edit → Project Settings → Time
Time.fixedDeltaTime = 0.01f; // 100 Hz (default: 0.02 = 50 Hz)
```

**Tradeoffs**:
- More frequent physics updates
- Better collision detection
- Higher CPU usage
- Affects entire project

#### 4. Use Raycasting

For instant-hit weapons:

```csharp
public class RaycastGun : MonoBehaviour
{
    [SerializeField] private float range = 100f;
    [SerializeField] private LayerMask hitLayers;

    void Shoot()
    {
        if (Physics.Raycast(transform.position, transform.forward, out RaycastHit hit, range, hitLayers))
        {
            // Instant hit, no tunneling possible
            if (hit.collider.TryGetComponent<IDamageable>(out var damageable))
            {
                damageable.TakeDamage(10);
            }
        }
    }
}
```

**Benefits**:
- No tunneling ever
- Instant hit
- Very accurate
- Good for hitscan weapons

**Drawbacks**:
- No bullet travel time
- Less visual feedback
- Different gameplay feel

## Bullet Detection Best Practices

### Why Triggers for Bullets

**Bullets are**:
- Fast (50+ units/sec)
- Lightweight (mass 0.01)
- Destroyed on impact
- Don't need physics reactions

**Benefits of Triggers**:
1. Guaranteed detection (no tunneling)
2. Better performance (no physics calculation)
3. Simple implementation
4. Stationary targets don't move

### Example Setup

**Bullet**:
```csharp
public class Bullet : MonoBehaviour
{
    [SerializeField] private float speed = 50f;
    [SerializeField] private float lifetime = 5f;
    [SerializeField] private int damage = 10;

    private Rigidbody rb;

    void Start()
    {
        rb = GetComponent<Rigidbody>();
        rb.linearVelocity = transform.forward * speed;
        Destroy(gameObject, lifetime);
    }

    // Destroy on any trigger collision
    private void OnTriggerEnter(Collider other)
    {
        if (other.TryGetComponent<IDamageable>(out var damageable))
        {
            damageable.TakeDamage(damage);
        }
        Destroy(gameObject);
    }
}
```

**Component Setup**:
- SphereCollider: `IsTrigger = false` (solid bullet)
- Rigidbody: `Use Gravity = false`, mass = 0.01
- Layer: "Bullet" (custom layer)

**Target (Barrel)**:
```csharp
public class Barrel : MonoBehaviour, IDamageable
{
    [SerializeField] private int health = 1;

    public void TakeDamage(int damage)
    {
        health -= damage;
        if (health <= 0)
        {
            Explode();
        }
    }

    private void Explode()
    {
        // Spawn explosion effect
        Destroy(gameObject);
    }
}
```

**Component Setup**:
- CapsuleCollider: `IsTrigger = true` (ghost collider for bullets)
- Rigidbody: Required for trigger detection
- Layer: "Damageable"

## Rigidbody Requirements

Both triggers and collisions require **at least one Rigidbody**.

### Valid Combinations

| Object A | Object B | Collision Detected? | Trigger Detected? |
|----------|----------|---------------------|-------------------|
| Rigidbody + Collider | Static Collider | ✅ Yes | ✅ Yes |
| Rigidbody + Trigger | Static Collider | ❌ No | ✅ Yes |
| Rigidbody + Collider | Rigidbody + Collider | ✅ Yes | ✅ Yes |
| Static Collider | Static Collider | ❌ No | ❌ No |
| Static Trigger | Static Collider | ❌ No | ❌ No |

**Rule**: At least one object must have a Rigidbody

### Kinematic Rigidbodies

```csharp
rb.isKinematic = true;
```

**Behavior**:
- Not affected by physics forces
- Can be moved via transform
- Still participates in collisions/triggers
- Good for moving platforms, elevators

**Use Cases**:
- Character controllers (root motion)
- Moving platforms
- Doors and elevators
- Objects that move via animation

## Multiple Colliders

You can have multiple colliders on one GameObject:

```csharp
// Example: Enemy with both trigger and collision
Enemy (Root)
├── BoxCollider (IsTrigger = false)  // Physics body
└── SphereCollider (IsTrigger = true) // Detection zone

// Example: Barrel with layered detection
Barrel (Root)
├── CapsuleCollider (IsTrigger = true)  // Bullet detection
└── BoxCollider (IsTrigger = false)     // Physics with environment
```

**Use Cases**:
- Detection zones around physical objects
- Different collision layers
- Separate bullet vs melee detection

## Layer-Based Collision

Configure which layers interact:

**Edit → Project Settings → Physics → Layer Collision Matrix**

```csharp
// Example layer setup
Layer 6: Bullet
Layer 7: Enemy
Layer 8: Environment

// Disable bullet-bullet collisions
// Enable bullet-enemy collisions
// Enable bullet-environment collisions
```

**Benefits**:
- Performance optimization
- Prevents unwanted interactions
- Clear collision logic

## Physics Materials

Control bounciness and friction:

```csharp
// Create Physics Material
// Right-click → Create → Physics Material

PhysicMaterial bouncyMaterial = new PhysicMaterial();
bouncyMaterial.bounciness = 0.8f;
bouncyMaterial.dynamicFriction = 0.3f;
bouncyMaterial.staticFriction = 0.3f;
bouncyMaterial.frictionCombine = PhysicMaterialCombine.Average;
bouncyMaterial.bounceCombine = PhysicMaterialCombine.Maximum;

// Assign to collider
GetComponent<Collider>().material = bouncyMaterial;
```

**Properties**:
- **Bounciness**: 0 (no bounce) to 1 (perfect bounce)
- **Dynamic Friction**: Friction when moving
- **Static Friction**: Friction when stationary
- **Combine**: How materials combine

## Performance Optimization

### Best Practices

**For Bullets**:
✅ Use triggers (cheaper than collisions)
✅ Use object pooling (avoid Instantiate/Destroy)
✅ Set short lifetime (clean up automatically)
✅ Layer-based collision matrix (avoid unnecessary checks)

**For Static Objects**:
✅ No Rigidbody if never moving
✅ Combine meshes when possible
✅ Use simple collider shapes (box, sphere, capsule)

**For Physics Objects**:
✅ Use appropriate collision detection mode
✅ Disable gravity if not needed
✅ Set objects to sleep when stationary
✅ Use compound colliders sparingly

### Collision Detection Mode by Use Case

| Use Case | Detection Mode |
|----------|---------------|
| Slow-moving objects | Discrete |
| Fast bullets | Continuous |
| Player/Characters | ContinuousSpeculative |
| Static objects | N/A (no Rigidbody) |
| Kinematic controllers | Discrete |

## Common Patterns

### Projectile Pattern

```csharp
// Fast bullet: Use trigger on target
Bullet: Solid collider + Rigidbody
Target: Trigger collider + Rigidbody

// Why: Guaranteed detection, good performance
```

### Pickup Pattern

```csharp
// Pickup item: Use trigger
Pickup: Trigger collider + Rigidbody
Player: Solid collider + Rigidbody

// Why: No physics interaction needed, detection only
```

### Explosive Force Pattern

```csharp
// Explosion affects nearby objects
public void Explode()
{
    Collider[] colliders = Physics.OverlapSphere(transform.position, radius);
    foreach (Collider col in colliders)
    {
        if (col.TryGetComponent<Rigidbody>(out var rb))
        {
            rb.AddExplosionForce(force, transform.position, radius);
        }
    }
}
```

## Debugging Physics

### Visualize Colliders

```csharp
// Gizmos in Scene view
private void OnDrawGizmos()
{
    Gizmos.color = Color.green;
    Gizmos.DrawWireSphere(transform.position, radius);
}

// Debug rays
Debug.DrawRay(origin, direction * distance, Color.red, duration);
```

### Physics Debugger

**Window → Analysis → Physics Debugger**

Shows:
- All Rigidbodies
- Collision shapes
- Contacts
- Forces

### Common Issues

**Objects fall through floor**:
- Check collision layers
- Verify Rigidbody settings
- Check for kinematic flag
- Ensure colliders are large enough

**Triggers not detecting**:
- Verify at least one Rigidbody
- Check layer collision matrix
- Ensure `IsTrigger = true`
- Check trigger callback methods exist

## Additional Resources

- [Unity Manual - Physics](https://docs.unity3d.com/Manual/PhysicsSection.html)
- [Unity Manual - Colliders](https://docs.unity3d.com/Manual/CollidersOverview.html)
- [Unity Manual - Rigidbody](https://docs.unity3d.com/Manual/class-Rigidbody.html)
- [Physics Best Practices](https://docs.unity3d.com/Manual/BestPracticeUnderstandingPerformanceInUnity6.html)
