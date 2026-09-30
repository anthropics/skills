# Flake playbook

## Common flake causes and fixes

### 1) Screen not ready
Fix:
- Wait for a screen anchor element to exist/hittable using predicates

### 2) Animations / transitions
Fix:
- Wait for anchor element on the destination screen (never arbitrary delays)

### 3) Element off-screen
Fix:
- Bounded scroll to make visible, then assert exists and hittable

### 4) Keyboard covering buttons
Fix:
- Dismiss keyboard (tap outside or use return key), then retry tap

### 5) System permission alerts
Fix:
- Handle alerts opportunistically (if present) and continue
