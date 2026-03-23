---
name: mobile-design
description: Design and build production-grade React Native + Expo mobile screens, components, and navigation flows. Use when the user asks to create, redesign, or audit a mobile UI - screens, components, navigation, animations, or design systems. Produces working NativeWind/StyleSheet code with accessibility, dark mode, and all UI states handled.
license: Complete terms in LICENSE.txt
---

This skill guides the design and implementation of production-grade React Native + Expo mobile interfaces. It produces working, accessible code that handles all UI states - not mockups or pseudocode.

The user provides a mobile UI task: a screen to build, a component to design, a navigation flow to map, or an existing screen to audit or improve.

## Design Thinking

Before writing code, commit to a clear design direction:

- **Platform**: iOS-first, Android-first, or cross-platform? (Affects shadows, fonts, navigation patterns)
- **Context**: What is the user doing on this screen? What did they just come from, where do they go next?
- **Hierarchy**: What is the single most important thing on screen? Design everything else to support it.
- **Touch model**: Which elements are interactive? Are tap targets >= 44x44pt?
- **States**: What does empty, loading, error, and fully-populated look like?

**CRITICAL**: Mobile screens have limited space. Ruthless prioritization beats feature-completeness. One clear action per screen beats five equal-weight actions.

## Styling Approach

Use **NativeWind** (Tailwind for React Native) for all styles unless the component requires animation (use `StyleSheet` only for Reanimated animated styles):

```tsx
// Preferred - NativeWind
<View className="flex-1 bg-background p-4">
  <Text className="text-xl font-semibold text-foreground">Title</Text>
</View>

// Only for Reanimated animated values
const animatedStyle = useAnimatedStyle(() => ({
  transform: [{ scale: scale.value }],
}));
```

### Spacing Scale

```
p-2 / gap-2 = 8px    (tight groupings)
p-3 / gap-3 = 12px   (related items)
p-4 / gap-4 = 16px   (standard padding)
p-6 / gap-6 = 24px   (section separation)
p-8 / gap-8 = 32px   (large breathing room)
```

### Border Radius

```
rounded-lg    -> inputs, small cards
rounded-xl    -> cards, list items, modals
rounded-2xl   -> large containers, bottom sheets
rounded-full  -> avatars, pills, icon buttons, FABs
```

### Typography

```
text-2xl font-bold      -> screen/page titles
text-xl  font-semibold  -> section headers
text-base font-medium   -> primary labels, body
text-sm                 -> secondary info, descriptions
text-xs                 -> timestamps, metadata, captions
```

## Screen Design

Structure every screen around four layers:

1. **Header** - Navigation context + title + optional action (back, close, menu)
2. **Content** - Primary content area (scrollable or fixed)
3. **Actions** - Primary CTA(s), bottom-anchored for thumb reach
4. **States** - Empty, loading, error variants of the content layer

### Layout Patterns

| Pattern | When to Use | Key Components |
|---------|-------------|---------------|
| List/Feed | Scrollable items, posts, history | `FlatList` + pull-to-refresh |
| Form | Data collection, settings | `ScrollView` + `KeyboardAvoidingView` |
| Modal/Sheet | Focused actions, confirmations | `Modal` or bottom sheet with drag handle |
| Dashboard | Multiple data types at a glance | `ScrollView` + card grid |
| Pager | Parallel sections (tabs) | `PagerView` or Tab navigator |
| Camera/Immersive | Media capture, full-bleed views | Absolute overlays on `CameraView` |
| Onboarding | Multi-step flows | Pager + progress indicator + skip |

### Screen Template

```tsx
import { View, Text, FlatList, ActivityIndicator, Pressable } from 'react-native';
import { SafeAreaView } from 'react-native-safe-area-context';

interface ScreenProps {
  // define props
}

export function ExampleScreen({}: ScreenProps) {
  const { data, isLoading, error, refetch } = useData();

  if (isLoading) return <LoadingState />;
  if (error) return <ErrorState message={error.message} onRetry={refetch} />;
  if (!data?.length) return <EmptyState />;

  return (
    <SafeAreaView className="flex-1 bg-background" edges={['top']}>
      {/* Header */}
      <View className="px-4 pb-3 flex-row items-center justify-between">
        <Text className="text-2xl font-bold text-foreground">Title</Text>
      </View>

      {/* Content */}
      <FlatList
        data={data}
        keyExtractor={(item) => item.id}
        renderItem={({ item }) => <ItemCard item={item} />}
        contentContainerClassName="px-4 gap-3 pb-8"
        showsVerticalScrollIndicator={false}
      />

      {/* Primary action */}
      <View className="px-4 pb-6 pt-3 border-t border-border">
        <Pressable
          onPress={handleAction}
          accessibilityRole="button"
          accessibilityLabel="Primary action"
          className="bg-primary rounded-xl py-4 items-center"
        >
          <Text className="text-white text-base font-semibold">Action</Text>
        </Pressable>
      </View>
    </SafeAreaView>
  );
}
```

## Component Design

Every component must define:
- **Props interface** - typed inputs and event callbacks
- **Variants** - default, active/selected, disabled, loading
- **Accessibility** - `accessibilityRole`, `accessibilityLabel`, `accessibilityState`

### Component Template

```tsx
import { Pressable, Text, View } from 'react-native';

interface CardProps {
  title: string;
  subtitle?: string;
  onPress?: () => void;
  variant?: 'default' | 'active' | 'disabled';
  isLoading?: boolean;
}

export function Card({
  title,
  subtitle,
  onPress,
  variant = 'default',
  isLoading = false,
}: CardProps) {
  return (
    <Pressable
      onPress={onPress}
      disabled={variant === 'disabled' || isLoading}
      accessibilityRole="button"
      accessibilityLabel={title}
      accessibilityState={{ disabled: variant === 'disabled' }}
      className={[
        'rounded-xl p-4 bg-card border border-border',
        variant === 'active' && 'border-primary bg-primary/10',
        variant === 'disabled' && 'opacity-50',
      ]
        .filter(Boolean)
        .join(' ')}
    >
      <Text className="text-base font-medium text-foreground">{title}</Text>
      {subtitle && (
        <Text className="text-sm text-muted-foreground mt-1">{subtitle}</Text>
      )}
    </Pressable>
  );
}
```

## UI States

Design all three states at the same time as the happy path - never defer them.

### Empty State

```tsx
function EmptyState({
  icon,
  title,
  subtitle,
  actionLabel,
  onAction,
}: {
  icon: string;
  title: string;
  subtitle: string;
  actionLabel?: string;
  onAction?: () => void;
}) {
  return (
    <View className="flex-1 items-center justify-center gap-3 px-8">
      <Text className="text-5xl">{icon}</Text>
      <Text className="text-xl font-semibold text-foreground text-center">{title}</Text>
      <Text className="text-sm text-muted-foreground text-center leading-relaxed">{subtitle}</Text>
      {actionLabel && (
        <Pressable
          onPress={onAction}
          accessibilityRole="button"
          className="mt-2 bg-primary rounded-xl px-6 py-3"
        >
          <Text className="text-white font-semibold">{actionLabel}</Text>
        </Pressable>
      )}
    </View>
  );
}
```

### Loading State (Skeleton)

```tsx
function SkeletonCard() {
  return (
    <View className="rounded-xl bg-card border border-border p-4 gap-3">
      <View className="h-4 bg-muted rounded-full w-3/4" />
      <View className="h-3 bg-muted rounded-full w-1/2" />
    </View>
  );
}

function LoadingState() {
  return (
    <View className="flex-1 items-center justify-center gap-3">
      <ActivityIndicator size="large" />
      <Text className="text-sm text-muted-foreground">Loading...</Text>
    </View>
  );
}
```

### Error State

```tsx
function ErrorState({
  message,
  onRetry,
}: {
  message: string;
  onRetry: () => void;
}) {
  return (
    <View className="flex-1 items-center justify-center gap-3 px-8">
      <Text className="text-4xl">[!]</Text>
      <Text className="text-xl font-semibold text-foreground text-center">
        Something went wrong
      </Text>
      <Text className="text-sm text-muted-foreground text-center">{message}</Text>
      <Pressable
        onPress={onRetry}
        accessibilityRole="button"
        className="bg-primary rounded-xl px-6 py-3"
      >
        <Text className="text-white font-semibold">Try Again</Text>
      </Pressable>
    </View>
  );
}
```

## Navigation Design (Expo Router)

Map every flow before writing code:

1. **Route names** - match the `app/` directory structure
2. **Navigation type**: push (drill-down), replace (no back), modal (overlay), dismiss
3. **Params** - typed with `useLocalSearchParams<{ id: string }>()`
4. **Guards** - back/dismiss warnings for unsaved changes

```tsx
// Navigate with typed params
router.push({ pathname: '/item/[id]', params: { id: item.id } });

// Modal presentation (set in _layout.tsx)
<Stack.Screen name="create" options={{ presentation: 'modal' }} />

// Read params
const { id } = useLocalSearchParams<{ id: string }>();

// Replace (no back stack entry)
router.replace('/home');
```

## Animations (react-native-reanimated)

Use shared values - never `useState` - for animated styles. Keep gestures on the UI thread.

```tsx
// Fade in on mount
const opacity = useSharedValue(0);
useEffect(() => { opacity.value = withTiming(1, { duration: 300 }); }, []);
const fadeStyle = useAnimatedStyle(() => ({ opacity: opacity.value }));

// Spring scale on press (satisfying tap feedback)
const scale = useSharedValue(1);
const pressStyle = useAnimatedStyle(() => ({ transform: [{ scale: scale.value }] }));
const handlers = useAnimatedGestureHandler({
  onStart: () => { scale.value = withSpring(0.96); },
  onEnd: () => { scale.value = withSpring(1); },
});

// Slide-up sheet
const translateY = useSharedValue(400);
useEffect(() => { translateY.value = withSpring(0, { damping: 20 }); }, []);
const sheetStyle = useAnimatedStyle(() => ({
  transform: [{ translateY: translateY.value }],
}));
```

## Accessibility

Every interactive element must have:
- `accessibilityRole`: `button`, `link`, `image`, `header`, `text`, `checkbox`, `radio`
- `accessibilityLabel`: meaningful description (not just the visible text if context is needed)
- `accessibilityState`: `{ disabled, selected, checked, busy }`
- Minimum **44x44pt** tap target - use `className="min-h-[44px] min-w-[44px]"` to enforce

```tsx
<Pressable
  accessibilityRole="button"
  accessibilityLabel="Delete photo"
  accessibilityState={{ disabled: isDeleting }}
  className="min-h-[44px] min-w-[44px] items-center justify-center"
>
  <TrashIcon />
</Pressable>
```

## Dark Mode

Design for dark mode from the start. Use semantic color tokens (`foreground`, `background`, `muted`, `card`, `border`, `primary`) - never hardcode hex values. If using a custom theme system, map it to CSS variables and toggle via a root class.

```tsx
// Good - token-based, works in both modes
<View className="bg-background">
  <Text className="text-foreground">Hello</Text>
  <Text className="text-muted-foreground">Subtitle</Text>
</View>

// Bad - breaks in dark mode
<View style={{ backgroundColor: '#ffffff' }}>
  <Text style={{ color: '#000000' }}>Hello</Text>
</View>
```

## Performance Guidelines

- Use `FlatList` or `FlashList` for any list > 10 items - never `ScrollView` + `map()`
- Never nest a `ScrollView` inside a `FlatList` (or vice versa) - causes gesture conflicts and jank
- `useCallback` on `renderItem` and `keyExtractor` to prevent unnecessary re-renders
- `removeClippedSubviews` on long lists
- Prefer `Pressable` over `TouchableOpacity` for new code

```tsx
// Good
<FlatList
  data={items}
  keyExtractor={useCallback((item) => item.id, [])}
  renderItem={useCallback(({ item }) => <ItemCard item={item} />, [])}
  removeClippedSubviews
/>

// Bad - unmounts/remounts everything on scroll
<ScrollView>
  {items.map((item) => <ItemCard key={item.id} item={item} />)}
</ScrollView>
```

## Output Format

- Always output **working, complete code** - no pseudocode, no ellipsis placeholders
- Include **all three states** (empty, loading, error) in every screen
- Show **before / after** when auditing existing code
- Annotate non-obvious decisions with `// why` comments
- Flag performance risks inline as `// WARN performance:`
- Flag accessibility gaps as `// WARN a11y:`
- Use `// TODO:` only for items that genuinely require external data to resolve

## Proactive Checks

When reviewing or building any mobile UI:

- **Hardcoded color** (`#`, `rgb(`, `hsl(`) -> replace with semantic token
- **Tap target < 44pt** -> add `min-h-[44px] min-w-[44px]`
- **Missing empty state** -> add before shipping
- **Missing loading state** -> add skeleton or spinner for async data
- **ScrollView wrapping a list** -> replace with `FlatList`
- **FlatList inside ScrollView** -> restructure layout
- **No `accessibilityRole` on Pressable** -> add it
- **Inline StyleSheet for non-animated styles** -> convert to NativeWind
- **`useState` driving an animation** -> replace with `useSharedValue`
