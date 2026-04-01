# Sensory Design Reference

## Table of Contents
1. UI Sound Design
2. Haptic Feedback
3. Multi-Sensory Integration

---

## 1. UI Sound Design

### Why Sound
Sound provides confirmation that an action occurred, draws attention to important state changes, and adds personality to the interface. It is underused on the web but highly effective when applied with restraint.

### The Soundcn Pattern
Use inline base64 audio data URIs with the Web Audio API. This avoids external file loading, CORS issues, and runtime fetching. Each sound is a self-contained TypeScript module.

```typescript
// sounds/click-soft.ts
export const clickSoftSound = "data:audio/wav;base64,UklGR..."; // base64 WAV

// hooks/use-sound.ts
import { useCallback, useRef } from 'react';

export function useSound(src: string) {
  const audioContextRef = useRef<AudioContext | null>(null);

  const play = useCallback(() => {
    if (!audioContextRef.current) {
      audioContextRef.current = new AudioContext();
    }
    const ctx = audioContextRef.current;
    fetch(src)
      .then(r => r.arrayBuffer())
      .then(buf => ctx.decodeAudioData(buf))
      .then(decoded => {
        const source = ctx.createBufferSource();
        source.buffer = decoded;
        source.connect(ctx.destination);
        source.start(0);
      });
  }, [src]);

  return [play] as const;
}
```

### Usage
```tsx
import { useSound } from "@/hooks/use-sound";
import { clickSoftSound } from "@/sounds/click-soft";

function Button() {
  const [play] = useSound(clickSoftSound);
  return <button onClick={() => { play(); handleAction(); }}>Save</button>;
}
```

### When to Use Sound
- **Button clicks**: soft, short click sound (50-100ms)
- **Success actions**: pleasant confirmation tone
- **Notifications**: attention-getting but not alarming chime
- **Errors**: subtle alert, not a harsh buzz
- **Toggle switches**: satisfying mechanical click
- **Transitions**: whoosh or swipe sound for page changes

### Rules
- Always provide a sound toggle in the UI (respect user preference)
- Keep sounds under 200ms for UI interactions
- Use the Web Audio API, not `<audio>` elements (lower latency)
- Sound volume should be subtle by default (0.3-0.5 of max)
- Never auto-play sounds on page load
- Source sounds from CC0 collections (Kenney, Freesound)

---

## 2. Haptic Feedback

### The Vibration API
```javascript
// Check support
if ('vibrate' in navigator) {
  // Simple tap (10ms pulse)
  navigator.vibrate(10);

  // Success pattern (two short pulses)
  navigator.vibrate([10, 50, 10]);

  // Error pattern (one longer pulse)
  navigator.vibrate(30);

  // Warning (three quick pulses)
  navigator.vibrate([10, 30, 10, 30, 10]);
}
```

### When to Use Haptics
- **Button press confirmation**: 10ms pulse on touch
- **Toggle switch**: 10ms pulse on state change
- **Destructive action confirmation**: 30ms pulse before confirmation dialog
- **Pull-to-refresh threshold**: 10ms pulse when the threshold is reached
- **Drag and drop**: 10ms pulse on pickup and drop

### Rules
- Gate behind feature detection (`'vibrate' in navigator`)
- Respect `prefers-reduced-motion` by disabling haptics when motion is reduced
- Keep durations very short (10-30ms for taps, never longer than 100ms)
- Do not use haptics for every interaction, only pivotal moments
- Mobile only: haptics have no effect on desktop

### iOS Considerations
The Vibration API has limited support on iOS Safari. For broader iOS support, use the experimental Haptic Feedback API or accept that haptics are Android-primary.

---

## 3. Multi-Sensory Integration

The strongest UI moments combine visual, auditory, and haptic feedback simultaneously:

1. User taps "Complete" button
2. **Visual**: checkmark animation scales in with a satisfying bounce
3. **Sound**: soft success chime (100ms)
4. **Haptic**: double-pulse pattern (10ms, 50ms gap, 10ms)

This triple feedback creates a moment of certainty that a single visual change cannot match. Use it sparingly, for milestone moments (order placed, task completed, level achieved).
