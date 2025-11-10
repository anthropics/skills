---
name: remotion-video-creator
description: Create programmatic video animations using React and Remotion. Use this skill when the user wants to create animated videos, motion graphics, or programmatic video content using React components. Supports text animations, transitions, data visualizations, and complex video compositions.
---

# Remotion Video Creator

This skill helps you create stunning programmatic videos using Remotion - a framework for making videos with React.

## What is Remotion?

Remotion allows you to create videos programmatically using:
- **React Components**: Build videos like you build web applications
- **Web Technologies**: Use CSS, Canvas, SVG, WebGL, and the entire React ecosystem
- **TypeScript**: Full type safety for your video projects
- **Programmatic Control**: Use variables, functions, APIs, and algorithms to create dynamic effects

## When to Use This Skill

Use this skill when the user wants to:
- Create animated videos programmatically
- Build text animations or kinetic typography
- Generate data visualizations as videos
- Create motion graphics or explainer videos
- Build video templates that can be rendered with different data
- Create social media content at scale
- Generate promotional videos or ads programmatically

## Core Workflow

### 1. Project Setup

When starting a new Remotion project:

```bash
# Create a new Remotion project
npx create-video@latest

# Or if working in an existing directory
npm init video

# Start development server
npm run dev
```

### 2. Understanding Remotion Structure

A typical Remotion project has this structure:
```
my-video/
├── src/
│   ├── Root.tsx          # Register compositions here
│   ├── Composition.tsx   # Your video components
│   └── ...
├── public/               # Static assets
├── remotion.config.ts    # Remotion configuration
├── package.json
└── tsconfig.json
```

### 3. Creating Video Compositions

Follow these steps when creating animations:

**Step 1: Define the Composition**

In `src/Root.tsx`, register your video composition:

```typescript
import { Composition } from 'remotion';
import { MyVideo } from './MyVideo';

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="MyVideo"
        component={MyVideo}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
```

**Step 2: Create the Video Component**

Use Remotion hooks and components to build animations:

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

export const MyVideo: React.FC = () => {
  const frame = useCurrentFrame();

  // Animate opacity from 0 to 1 over first 30 frames
  const opacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill style={{ backgroundColor: 'white' }}>
      <div style={{ opacity }}>
        <h1>Hello, Remotion!</h1>
      </div>
    </AbsoluteFill>
  );
};
```

### 4. Animation Techniques

**Using interpolate()** for smooth transitions:
```typescript
const scale = interpolate(frame, [0, 30, 60], [0, 1, 1.5]);
const rotation = interpolate(frame, [0, 100], [0, 360]);
```

**Using spring()** for natural motion:
```typescript
import { spring, useVideoConfig } from 'remotion';

const { fps } = useVideoConfig();
const progress = spring({
  frame,
  fps,
  config: {
    damping: 100,
    stiffness: 200,
    mass: 0.5,
  },
});
```

**Using Sequence** for timing:
```typescript
import { Sequence } from 'remotion';

<Sequence from={0} durationInFrames={60}>
  <Scene1 />
</Sequence>
<Sequence from={60} durationInFrames={60}>
  <Scene2 />
</Sequence>
```

### 5. Rendering Videos

To render the final video:

```bash
# Render a specific composition
npx remotion render MyVideo out/video.mp4

# Render with custom settings
npx remotion render MyVideo out/video.mp4 --codec=h264 --quality=90
```

## Best Practices

1. **Keep Components Pure**: Video components should be deterministic - same frame always produces same output
2. **Use Absolute Positioning**: Use `<AbsoluteFill>` for layout to ensure consistent rendering
3. **Optimize Performance**: Keep frame renders fast; avoid heavy computations
4. **Use TypeScript**: Leverage type safety for props and configurations
5. **Test Frame by Frame**: Use the Remotion Player to scrub through and test specific frames
6. **Separate Data from Presentation**: Pass data as props to make compositions reusable
7. **Use the right FPS**: 30fps for web content, 60fps for smooth motion, 24fps for cinematic feel

## Common Animation Patterns

### Text Fade In
```typescript
const opacity = interpolate(frame, [0, 30], [0, 1], {
  extrapolateRight: 'clamp',
});
```

### Slide In from Left
```typescript
const translateX = interpolate(frame, [0, 30], [-100, 0], {
  extrapolateRight: 'clamp',
});
```

### Scale and Bounce
```typescript
const scale = spring({
  frame,
  fps,
  from: 0,
  to: 1,
});
```

### Stagger Animations
```typescript
{items.map((item, i) => {
  const delay = i * 10; // 10 frame delay between items
  return (
    <Sequence key={i} from={delay}>
      <AnimatedItem item={item} />
    </Sequence>
  );
})}
```

## Important Concepts

### Frame-based Timing
- Everything in Remotion is based on frames, not seconds
- Use `useCurrentFrame()` to get the current frame number
- Calculate time: `seconds = frame / fps`

### Compositions
- Each composition is a registered video that can be rendered
- Compositions have metadata: width, height, fps, duration
- You can have multiple compositions in one project

### Sequences
- Use `<Sequence>` to time-shift content
- Nested sequences cascade their timing
- Use `durationInFrames` to automatically unmount components

### Interpolation
- `interpolate()` maps input range to output range
- Supports easing functions for smooth transitions
- Can extrapolate or clamp values outside the range

## Reference Documentation

For detailed information, refer to:
- `reference/core-concepts.md` - Core Remotion concepts and APIs
- `reference/api-reference.md` - Complete API documentation
- `reference/best-practices.md` - Advanced patterns and optimization tips

## Templates

Ready-to-use templates are available in the `templates/` directory:
- `templates/text-animation.md` - Text and typography animations
- `templates/graphic-animation.md` - Shape and graphic animations
- `templates/transitions.md` - Scene transitions and effects

## Development Tips

1. **Live Preview**: The dev server (`npm run dev`) provides instant feedback
2. **Timeline Scrubbing**: Use the timeline to jump to any frame
3. **Fast Refresh**: Changes appear instantly without losing state
4. **Console Logging**: Debug by logging the current frame value
5. **Component Composition**: Build complex scenes from simple reusable components

## Rendering Options

Remotion supports various rendering methods:
- **Local Rendering**: `npx remotion render` on your machine
- **Lambda Rendering**: Serverless rendering on AWS Lambda
- **Cloud Run**: Rendering on Google Cloud Run
- **CI/CD Integration**: Automate video generation in your pipeline

## Getting Help

If you encounter issues:
1. Check the official documentation at https://remotion.dev/docs
2. Review the examples at https://remotion.dev/docs/resources
3. Join the Remotion Discord community
4. Search GitHub issues at https://github.com/remotion-dev/remotion

## License Note

Remotion requires a commercial license for certain use cases. Make sure to review the licensing requirements at https://remotion.dev/license if creating videos for commercial purposes.

---

## Implementation Guidelines

When helping users create Remotion videos:

1. **Understand Requirements**: Ask about video dimensions, duration, frame rate, and content type
2. **Plan Structure**: Break down the video into scenes/sequences
3. **Choose Animation Style**: Decide between interpolate (linear/eased) and spring (natural motion)
4. **Build Incrementally**: Start simple, test often, add complexity gradually
5. **Optimize**: Keep renders fast by avoiding unnecessary re-renders and heavy computations
6. **Test Thoroughly**: Scrub through the entire timeline to check all frames
7. **Provide Clear Code**: Write clean, well-commented, type-safe code

Remember: Remotion videos are React components. If you can build it in React, you can animate it in Remotion!
