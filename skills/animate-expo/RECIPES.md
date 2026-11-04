# Expo Animation Recipes

Ready-to-build implementations for the cases that come up most in a React Native app. Start from the recipe, then adapt.

---

## Setup the recipes assume

```bash
npx expo install react-native-reanimated react-native-worklets react-native-gesture-handler expo-haptics
```

(`react-native-keyboard-controller` only for the keyboard recipe.) `expo install`, not `npm install` — it resolves the versions that match the SDK. The worklets Babel plugin is configured by `babel-preset-expo` automatically.

`GestureHandlerRootView` wraps the app once — in Expo Router, the root `_layout`:

```jsx
import { GestureHandlerRootView } from 'react-native-gesture-handler';

export default function RootLayout() {
  return (
    <GestureHandlerRootView style={{ flex: 1 }}>
      <Stack />
    </GestureHandlerRootView>
  );
}
```

Imports and constants every recipe below shares:

```js
import { useState, useEffect, useMemo } from 'react';
import Animated, {
  useSharedValue, useAnimatedStyle, useAnimatedScrollHandler, useAnimatedReaction,
  withSpring, withTiming, interpolate, Extrapolation, Easing,
  FadeInDown, FadeOutDown, LinearTransition,
} from 'react-native-reanimated';
import { Gesture, GestureDetector } from 'react-native-gesture-handler';
import { scheduleOnRN } from 'react-native-worklets';
import * as Haptics from 'expo-haptics';

const EASE_OUT = Easing.bezier(0.23, 1, 0.32, 1);      // strong ease-out for UI
const EASE_IN_OUT = Easing.bezier(0.77, 0, 0.175, 1);  // on-screen movement
const EASE_SHEET = Easing.bezier(0.32, 0.72, 0, 1);    // iOS sheet curve
```

Three conventions, explained once here instead of in every recipe:

- **Shared values are read and written with `.get()` / `.set()`**, the form the Reanimated docs recommend for React Compiler support. `.value` still works, but the compiler can't see through it.
- **`scheduleOnRN(fn, ...args)` replaces the deprecated `runOnJS(fn)(...args)`** for calling back to the React Native runtime from a worklet.
- **Gestures are wrapped in `useMemo`.** Rebuilding a gesture on every render can reattach the recognizer and drop a drag that's mid-flight.

**Gesture Handler v3:** Expo installs v2, and the recipes use its `Gesture.Pan()` builder. If the project is already on v3, the builder is legacy — each gesture is a hook taking one config object, with `onStart` → `onActivate`, `onEnd` → `onDeactivate`, and the `success` flag replaced by `event.canceled` (inverted). The hook manages its own identity, so drop the `useMemo`:

```jsx
const pan = usePanGesture({
  activeOffsetY: [-10, 10],
  onActivate: () => { context.set(translateY.get()); },
  onUpdate: (e) => { translateY.set(context.get() + e.translationY); },
  onDeactivate: (e) => { /* settle with withSpring as below */ },
});
```

---

## Two worklets you'll need everywhere

Momentum projection decides *where a flick was going*, so a fast short swipe commits and a slow long one doesn't. Rubber-banding makes a boundary resist instead of stopping dead.

```js
// Where the finger would come to rest if it kept decelerating.
// Apple's exponential-decay form — not the v²/2a from physics class.
function project(velocity, decelerationRate = 0.998) {
  'worklet';
  return ((velocity / 1000) * decelerationRate) / (1 - decelerationRate);
}

// The further past the edge, the less the element follows.
function rubberband(overshoot, dimension, constant = 0.55) {
  'worklet';
  return (overshoot * dimension * constant) / (dimension + constant * Math.abs(overshoot));
}
```

---

## Press feedback

Every pressable in the app. This passes the frequency gate only because it's near-imperceptible: 120ms and a 3% scale is the ceiling for something touched this often — anything longer or larger belongs to rarer moments, per step 1 in SKILL.md. No gesture, no shared value — a CSS transition is the whole implementation.

```jsx
import Animated from 'react-native-reanimated';
import { Pressable, StyleSheet } from 'react-native';

function PressableScale({ onPress, children }) {
  const [pressed, setPressed] = useState(false);
  return (
    <Pressable
      onPress={onPress}
      onPressIn={() => setPressed(true)}
      onPressOut={() => setPressed(false)}
      hitSlop={12}
      pressRetentionOffset={16}
    >
      <Animated.View style={[styles.box, pressed && styles.pressed]}>{children}</Animated.View>
    </Pressable>
  );
}

const styles = StyleSheet.create({
  box: {
    transform: [{ scale: 1 }],
    transitionProperty: 'transform',
    transitionDuration: '120ms',
    transitionTimingFunction: 'cubic-bezier(0.23, 1, 0.32, 1)',
  },
  pressed: { transform: [{ scale: 0.97 }] },
});
```

`setState` is fine here — it fires twice per press, not per frame. `hitSlop` brings a small icon up to the 44pt target without growing it; `pressRetentionOffset` stops a slight finger drift from cancelling.

---

## Bottom sheet you can drag to dismiss

Before writing this: if the sheet is its own destination, use `presentation: 'formSheet'` (see **Screen transitions**) and get the platform's real sheet for free. Build this only when the sheet has to live inside an existing screen.

```jsx
const translateY = useSharedValue(0);
const context = useSharedValue(0);

const pan = useMemo(() => Gesture.Pan()
  .activeOffsetY([-10, 10])   // let a horizontal swipe win; require intent before committing
  .onStart(() => {
    context.set(translateY.get());   // start from the current on-screen value, not from 0
  })
  .onUpdate((e) => {
    const next = context.get() + e.translationY;
    // downward is free; upward past the top resists
    translateY.set(next >= 0 ? next : rubberband(next, HEIGHT));
  })
  .onEnd((e) => {
    const projected = translateY.get() + project(e.velocityY);
    if (projected > HEIGHT * 0.4) {
      translateY.set(withSpring(HEIGHT, {
        duration: 300, dampingRatio: 1, velocity: e.velocityY, overshootClamping: true,
      }, (finished) => { if (finished) scheduleOnRN(onClose); }));
    } else {
      translateY.set(withSpring(0, { duration: 300, dampingRatio: 0.8, velocity: e.velocityY }));
      scheduleOnRN(Haptics.impactAsync, Haptics.ImpactFeedbackStyle.Light);   // it snapped home
    }
  }), [onClose]);

const sheetStyle = useAnimatedStyle(() => ({ transform: [{ translateY: translateY.get() }] }));
```

The four details that separate this from a bad drag:

- **`onStart` captures the current value.** Without it, grabbing a sheet mid-animation teleports it — the animation must continue from where the eye last saw it.
- **Velocity decides, not distance.** `project()` means a quick flick dismisses even a few pixels down. Requiring 40% travel makes the sheet feel heavy.
- **Velocity is handed to the spring**, so there's no seam between the finger releasing and the animation continuing. This is the single detail that most separates "fluid" from "fine".
- **`overshootClamping` on dismissal** — otherwise the sheet springs past the bottom of the screen and flashes a gap.

The backdrop derives from the same value, so it's always in sync and costs nothing:

```jsx
const backdropStyle = useAnimatedStyle(() => ({
  opacity: interpolate(translateY.get(), [0, HEIGHT], [1, 0], Extrapolation.CLAMP),
}));
```

---

## Swipe to delete a row

Before writing this: gesture-handler ships [`ReanimatedSwipeable`](https://docs.swmansion.com/react-native-gesture-handler/docs/components/reanimated_swipeable/), which already does swipe-to-reveal actions — thresholds, overshoot, open/close methods — on the UI thread. Reach for it when the row reveals action buttons. Build the gesture yourself only when the interaction is different in kind: swipe-to-commit with momentum projection, like this one.

```jsx
const x = useSharedValue(0);
const context = useSharedValue(0);

const pan = useMemo(() => Gesture.Pan()
  .activeOffsetX([-10, 10])   // must declare the axis, or it fights the vertical scroll
  .onStart(() => { context.set(x.get()); })   // grab mid-spring continues from where the row is, not from 0
  .onUpdate((e) => { x.set(Math.min(0, context.get() + e.translationX)); })
  .onEnd((e) => {
    const projected = x.get() + project(e.velocityX);
    if (projected < -SWIPE_THRESHOLD) {
      x.set(withTiming(-WIDTH, { duration: 200, easing: EASE_OUT }, (f) => {
        if (f) scheduleOnRN(onDelete, id);
      }));
    } else {
      x.set(withSpring(0, { duration: 300, dampingRatio: 1, velocity: e.velocityX }));
    }
  }), [onDelete, id]);
```

Closing the gap the deleted row left is the list's job, not the row's:

```jsx
const ROW_CLOSE = LinearTransition.duration(200);   // module scope — builders rebuilt in render cost every re-render

<Animated.FlatList data={items} itemLayoutAnimation={ROW_CLOSE} ... />
```

`activeOffsetX` is the mobile-specific part. A pan handler inside a scroll view with no axis declared will steal vertical scrolls, and the list will feel broken in a way that looks like a scrolling bug rather than a gesture bug.

---

## Collapsing header on scroll

```jsx
const scrollY = useSharedValue(0);
const onScroll = useAnimatedScrollHandler((e) => { scrollY.set(e.contentOffset.y); });

const titleStyle = useAnimatedStyle(() => ({
  opacity: interpolate(scrollY.get(), [0, 60], [1, 0], Extrapolation.CLAMP),
  transform: [{ translateY: interpolate(scrollY.get(), [0, 60], [0, -12], Extrapolation.CLAMP) }],
}));

<Animated.ScrollView onScroll={onScroll} scrollEventThrottle={16}>
```

**Never animate the header's `height` to collapse it.** That runs a layout pass on the header and everything below it on every scroll frame — the one animation guaranteed to stutter, because it's competing with the scroll itself. Give the container a fixed height and translate the content inside it, clipping with `overflow: 'hidden'`.

`Extrapolation.CLAMP` is not optional: without it, scrolling past 60 keeps driving opacity negative and the header reappears inverted at the bottom of a long list.

---

## List entrances

```jsx
// The Reanimated docs recommend building layout animations outside components,
// or in useMemo — an inline chain in JSX rebuilds the builder on every render.
// A per-index delay can't live at module scope, so the row memoizes its own:
function Row({ item, index }) {
  const entering = useMemo(() => FadeInDown.duration(250).delay(index * 40), [index]);
  return <Animated.View entering={entering}>{/* ... */}</Animated.View>;
}

{items.map((item, i) => <Row key={item.id} item={item} index={i} />)}
```

Stagger 30–80ms. Longer feels slow, shorter reads as simultaneous.

**Never put `entering` on a row inside `FlatList`, `FlashList`, or any virtualized list.** Rows are recycled, so the animation re-fires every time one scrolls back into view — the list appears to flicker while the user scrolls. Animate the list container once on mount, or use `itemLayoutAnimation` for reflow only.

Entrance animations are for content the user asked for and is waiting on. A list they scroll past all day should already be there.

---

## Keyboard-synced UI

Needs its own module and a one-time provider ([Expo keyboard guide](https://docs.expo.dev/guides/keyboard-handling/)):

```bash
npx expo install react-native-keyboard-controller
```

```jsx
import { KeyboardProvider } from 'react-native-keyboard-controller';

// Root _layout, next to GestureHandlerRootView — hooks below do nothing without it.
<KeyboardProvider>
  <Stack />
</KeyboardProvider>
```

```jsx
import { useReanimatedKeyboardAnimation } from 'react-native-keyboard-controller';

const { height } = useReanimatedKeyboardAnimation();   // 0 → -keyboardHeight, on the UI thread
const footerStyle = useAnimatedStyle(() => ({ transform: [{ translateY: height.get() }] }));
```

Never build this from `Keyboard.addListener` plus a timing animation. The keyboard rides a private system curve, the event arrives on the JS thread after the keyboard has already started moving, and any duration you pick will visibly lag or lead it. The UI must be driven by the keyboard's actual position, frame by frame.

---

## Tab / segmented indicator

Measure once, then animate transforms.

```jsx
const [layouts, setLayouts] = useState({});   // measured with onLayout, not per frame
const x = useSharedValue(0);
const w = useSharedValue(0);

useEffect(() => {
  const l = layouts[active];
  if (!l) return;
  x.set(withTiming(l.x, { duration: 250, easing: EASE_IN_OUT }));
  w.set(withTiming(l.width, { duration: 250, easing: EASE_IN_OUT }));
}, [active, layouts]);

const pillStyle = useAnimatedStyle(() => ({
  transform: [{ translateX: x.get() }],
  width: w.get(),
}));
```

This is the sanctioned `width` animation: the pill is absolutely positioned with no children, so nothing else re-lays-out, and its corner radius survives — `scaleX` would smear the corners into ovals.

`ease-in-out`, because the pill is moving across the screen rather than entering or leaving it. Fire `Haptics.selectionAsync()` on the press, not when the pill lands.

---

## Screen transitions (Expo Router)

Configure the native stack. Never rebuild a screen transition in JS: the native one runs on the platform side, keeps the interactive back gesture, and matches every other app on the device.

```jsx
<Stack screenOptions={{ animation: reduced ? 'fade' : 'default' }}>
  <Stack.Screen name="settings" options={{ animation: 'slide_from_right', animationMatchesGesture: true }} />
  <Stack.Screen name="compose" options={{ presentation: 'modal' }} />
  <Stack.Screen name="filter" options={{
    presentation: 'formSheet',
    sheetAllowedDetents: 'fitToContents',
    sheetGrabberVisible: true,
  }} />
</Stack>
```

| Navigation | Option |
| --- | --- |
| Deeper into a hierarchy | `animation: 'default'` — the platform push, unmodified |
| A self-contained task the user can abandon | `presentation: 'modal'` |
| A short interruption: picker, filter, share | `presentation: 'formSheet'` with detents |
| Between tabs | `animation: 'none'` |
| Reduced motion | `animation: 'fade'` |

`animationMatchesGesture: true` makes the iOS back swipe run your transition in reverse under the finger, instead of the default push. Set it whenever you set a custom `animation`, or dragging back looks like a different app than pushing forward.

`formSheet` is native on both platforms, but not the same on both — the [Expo modal docs](https://docs.expo.dev/router/advanced/modals/#form-sheet-presentation) have the full list:

- **Android caps detents at three.** A longer `sheetAllowedDetents` array works on iOS and silently truncates on Android — design for three.
- **`sheetGrabberVisible` is iOS-only.** Android shows no grabber; don't rely on it as the only "this is draggable" affordance.
- **Android form sheets can't host native headers or nested stacks.** Keep the sheet's content a single screen; if it needs its own navigation, use `presentation: 'modal'` instead.
- **`fitToContents` needs explicitly sized content.** A `flex: 1` root has no intrinsic height to fit — size the content, or the detent is wrong.

---

## Toast

```jsx
// Module scope — layout-animation builders live outside the component.
const TOAST_ENTER = FadeInDown.duration(300).easing(EASE_OUT);
const TOAST_EXIT = FadeOutDown.duration(250).easing(EASE_OUT);

<Animated.View
  entering={TOAST_ENTER}
  exiting={TOAST_EXIT}
  style={{ position: 'absolute', bottom: insets.bottom + 16, left: 16, right: 16 }}
/>
```

- **The 300ms cap holds here too.** A toast isn't an exception — it's uninvited, so if anything it should be quicker and quieter than motion the user asked for.
- **It exits the way it entered.** Entering from the bottom and leaving to the side reads as two unrelated elements.
- **Exit ~20% faster than entry.** The user has finished reading; the arrival deserves the time, the departure doesn't.
- **Safe area insets, always.** A toast at `bottom: 16` sits under the home indicator on every modern iPhone.

If toasts stack and the list reflows, add `itemLayoutAnimation` and expect to tune the opacity against the reflow by eye — there's no formula for that pair. Look at it again the next day.

---

## Firing something once at a threshold

When a crossing point matters — a detent, a snap, a pull-to-refresh arming — don't poll it from JS and don't `scheduleOnRN` every frame.

```jsx
const armed = useSharedValue(false);

useAnimatedReaction(
  () => pullDistance.get() > REFRESH_THRESHOLD,
  (isArmed, wasArmed) => {
    if (isArmed !== wasArmed) {
      armed.set(isArmed);
      scheduleOnRN(Haptics.impactAsync, Haptics.ImpactFeedbackStyle.Light);
    }
  }
);
```

The comparison runs on the UI thread every frame; the JS call happens twice per pull. That's the pattern for every "do something when the animation reaches X".
