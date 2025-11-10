# Text Animation Templates

Ready-to-use text animation patterns for Remotion videos.

## 1. Fade In Text

Simple fade-in animation for text.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface FadeInTextProps {
  text: string;
  delay?: number;
  duration?: number;
}

export const FadeInText: React.FC<FadeInTextProps> = ({
  text,
  delay = 0,
  duration = 30,
}) => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - delay);

  const opacity = interpolate(localFrame, [0, duration], [0, 1], {
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      <h1
        style={{
          fontSize: 100,
          fontWeight: 'bold',
          opacity,
        }}
      >
        {text}
      </h1>
    </AbsoluteFill>
  );
};
```

---

## 2. Slide In Text

Text slides in from a direction.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

type Direction = 'left' | 'right' | 'top' | 'bottom';

interface SlideInTextProps {
  text: string;
  direction?: Direction;
  delay?: number;
  duration?: number;
}

export const SlideInText: React.FC<SlideInTextProps> = ({
  text,
  direction = 'left',
  delay = 0,
  duration = 30,
}) => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - delay);

  const getTransform = () => {
    const progress = interpolate(localFrame, [0, duration], [0, 1], {
      extrapolateRight: 'clamp',
    });

    switch (direction) {
      case 'left':
        return `translateX(${interpolate(progress, [0, 1], [-100, 0])}%)`;
      case 'right':
        return `translateX(${interpolate(progress, [0, 1], [100, 0])}%)`;
      case 'top':
        return `translateY(${interpolate(progress, [0, 1], [-100, 0])}%)`;
      case 'bottom':
        return `translateY(${interpolate(progress, [0, 1], [100, 0])}%)`;
    }
  };

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      <h1
        style={{
          fontSize: 100,
          fontWeight: 'bold',
          transform: getTransform(),
        }}
      >
        {text}
      </h1>
    </AbsoluteFill>
  );
};
```

---

## 3. Typewriter Effect

Text appears character by character.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface TypewriterTextProps {
  text: string;
  delay?: number;
  charactersPerFrame?: number;
}

export const TypewriterText: React.FC<TypewriterTextProps> = ({
  text,
  delay = 0,
  charactersPerFrame = 0.5,
}) => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - delay);

  const charactersToShow = Math.floor(localFrame * charactersPerFrame);
  const displayedText = text.slice(0, charactersToShow);

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
        backgroundColor: '#000',
        color: '#0f0',
        fontFamily: 'monospace',
      }}
    >
      <div style={{ fontSize: 60 }}>
        {displayedText}
        {charactersToShow < text.length && (
          <span style={{ opacity: (localFrame % 2) > 1 ? 1 : 0 }}>|</span>
        )}
      </div>
    </AbsoluteFill>
  );
};
```

---

## 4. Scale and Bounce Text

Text scales up with a spring animation.

```typescript
import { useCurrentFrame, useVideoConfig, spring, AbsoluteFill } from 'remotion';

interface BounceTextProps {
  text: string;
  delay?: number;
}

export const BounceText: React.FC<BounceTextProps> = ({
  text,
  delay = 0,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const localFrame = Math.max(0, frame - delay);

  const scale = spring({
    frame: localFrame,
    fps,
    config: {
      damping: 12,
      stiffness: 200,
      mass: 0.5,
    },
  });

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      <h1
        style={{
          fontSize: 100,
          fontWeight: 'bold',
          transform: `scale(${scale})`,
        }}
      >
        {text}
      </h1>
    </AbsoluteFill>
  );
};
```

---

## 5. Rotating Text

Text rotates in 3D space.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface RotatingTextProps {
  text: string;
  delay?: number;
  duration?: number;
}

export const RotatingText: React.FC<RotatingTextProps> = ({
  text,
  delay = 0,
  duration = 60,
}) => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - delay);

  const rotationY = interpolate(localFrame, [0, duration], [90, 0], {
    extrapolateRight: 'clamp',
  });

  const opacity = interpolate(localFrame, [0, duration / 2], [0, 1], {
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
        perspective: 1000,
      }}
    >
      <h1
        style={{
          fontSize: 100,
          fontWeight: 'bold',
          transform: `rotateY(${rotationY}deg)`,
          opacity,
        }}
      >
        {text}
      </h1>
    </AbsoluteFill>
  );
};
```

---

## 6. Word-by-Word Reveal

Each word appears sequentially.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface WordRevealProps {
  text: string;
  delay?: number;
  framesPerWord?: number;
}

export const WordReveal: React.FC<WordRevealProps> = ({
  text,
  delay = 0,
  framesPerWord = 15,
}) => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - delay);

  const words = text.split(' ');
  const currentWordIndex = Math.floor(localFrame / framesPerWord);

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      <h1 style={{ fontSize: 80, fontWeight: 'bold', textAlign: 'center' }}>
        {words.map((word, index) => {
          const wordFrame = localFrame - index * framesPerWord;
          const opacity = interpolate(wordFrame, [0, framesPerWord / 2], [0, 1], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          });

          return (
            <span key={index} style={{ opacity, marginRight: 20 }}>
              {word}
            </span>
          );
        })}
      </h1>
    </AbsoluteFill>
  );
};
```

---

## 7. Glitch Text Effect

Creates a glitch/distortion effect.

```typescript
import { useCurrentFrame, random, AbsoluteFill } from 'remotion';

interface GlitchTextProps {
  text: string;
  intensity?: number;
}

export const GlitchText: React.FC<GlitchTextProps> = ({
  text,
  intensity = 5,
}) => {
  const frame = useCurrentFrame();

  // Glitch occurs randomly
  const isGlitching = random(`glitch-${Math.floor(frame / 3)}`) > 0.7;

  const offsetX = isGlitching ? (random(`x-${frame}`) - 0.5) * intensity * 2 : 0;
  const offsetY = isGlitching ? (random(`y-${frame}`) - 0.5) * intensity * 2 : 0;

  const rgbSplit = isGlitching ? intensity : 0;

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
        backgroundColor: '#000',
      }}
    >
      <div style={{ position: 'relative' }}>
        {/* Red channel */}
        <h1
          style={{
            fontSize: 100,
            fontWeight: 'bold',
            color: '#ff0000',
            position: 'absolute',
            left: -rgbSplit,
            mixBlendMode: 'screen',
          }}
        >
          {text}
        </h1>

        {/* Green channel */}
        <h1
          style={{
            fontSize: 100,
            fontWeight: 'bold',
            color: '#00ff00',
            position: 'absolute',
            mixBlendMode: 'screen',
          }}
        >
          {text}
        </h1>

        {/* Blue channel */}
        <h1
          style={{
            fontSize: 100,
            fontWeight: 'bold',
            color: '#0000ff',
            position: 'absolute',
            left: rgbSplit,
            mixBlendMode: 'screen',
            transform: `translate(${offsetX}px, ${offsetY}px)`,
          }}
        >
          {text}
        </h1>

        {/* Main text */}
        <h1
          style={{
            fontSize: 100,
            fontWeight: 'bold',
            color: '#fff',
            opacity: 0,
          }}
        >
          {text}
        </h1>
      </div>
    </AbsoluteFill>
  );
};
```

---

## 8. Gradient Text Animation

Text with animated gradient.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface GradientTextProps {
  text: string;
}

export const GradientText: React.FC<GradientTextProps> = ({ text }) => {
  const frame = useCurrentFrame();

  const hue = interpolate(frame, [0, 120], [0, 360]) % 360;

  const gradientStyle: React.CSSProperties = {
    fontSize: 120,
    fontWeight: 'bold',
    background: `linear-gradient(45deg,
      hsl(${hue}, 100%, 50%),
      hsl(${(hue + 60) % 360}, 100%, 50%),
      hsl(${(hue + 120) % 360}, 100%, 50%)
    )`,
    WebkitBackgroundClip: 'text',
    WebkitTextFillColor: 'transparent',
    backgroundClip: 'text',
  };

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
        backgroundColor: '#000',
      }}
    >
      <h1 style={gradientStyle}>{text}</h1>
    </AbsoluteFill>
  );
};
```

---

## 9. Staggered Letter Animation

Each letter animates individually with a delay.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface StaggeredLettersProps {
  text: string;
  staggerDelay?: number;
}

export const StaggeredLetters: React.FC<StaggeredLettersProps> = ({
  text,
  staggerDelay = 2,
}) => {
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      <h1 style={{ fontSize: 100, fontWeight: 'bold', display: 'flex' }}>
        {text.split('').map((letter, index) => {
          const letterFrame = Math.max(0, frame - index * staggerDelay);

          const translateY = interpolate(letterFrame, [0, 20], [100, 0], {
            extrapolateRight: 'clamp',
          });

          const opacity = interpolate(letterFrame, [0, 15], [0, 1], {
            extrapolateRight: 'clamp',
          });

          return (
            <span
              key={index}
              style={{
                display: 'inline-block',
                transform: `translateY(${translateY}px)`,
                opacity,
              }}
            >
              {letter === ' ' ? '\u00A0' : letter}
            </span>
          );
        })}
      </h1>
    </AbsoluteFill>
  );
};
```

---

## 10. Kinetic Typography

Dynamic text with multiple animations combined.

```typescript
import { useCurrentFrame, useVideoConfig, interpolate, spring, AbsoluteFill } from 'remotion';

interface KineticTypographyProps {
  lines: string[];
}

export const KineticTypography: React.FC<KineticTypographyProps> = ({ lines }) => {
  const frame = useCurrentFrame();
  const { fps, width, height } = useVideoConfig();

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a1a' }}>
      {lines.map((line, index) => {
        const delay = index * 30;
        const localFrame = Math.max(0, frame - delay);

        // Different animation for each line
        const animations = [
          // Line 0: Scale and fade
          () => {
            const scale = spring({ frame: localFrame, fps, config: { damping: 15 } });
            const opacity = interpolate(localFrame, [0, 15], [0, 1], {
              extrapolateRight: 'clamp',
            });
            return { transform: `scale(${scale})`, opacity };
          },
          // Line 1: Slide from left
          () => {
            const x = interpolate(localFrame, [0, 30], [-width, 0], {
              extrapolateRight: 'clamp',
            });
            return { transform: `translateX(${x}px)` };
          },
          // Line 2: Rotate
          () => {
            const rotation = interpolate(localFrame, [0, 30], [180, 0], {
              extrapolateRight: 'clamp',
            });
            const opacity = interpolate(localFrame, [0, 20], [0, 1], {
              extrapolateRight: 'clamp',
            });
            return { transform: `rotate(${rotation}deg)`, opacity };
          },
        ];

        const animationStyle = animations[index % animations.length]();

        return (
          <div
            key={index}
            style={{
              position: 'absolute',
              top: height / 2 - 100 + index * 80,
              left: width / 2,
              fontSize: 60,
              fontWeight: 'bold',
              color: '#fff',
              ...animationStyle,
              transformOrigin: 'center',
            }}
          >
            {line}
          </div>
        );
      })}
    </AbsoluteFill>
  );
};
```

---

## Usage Example

Combine multiple text animations in a composition:

```typescript
import { Composition } from 'remotion';
import { Sequence, AbsoluteFill } from 'remotion';
import {
  FadeInText,
  SlideInText,
  TypewriterText,
  BounceText,
} from './TextAnimations';

export const TextShowcase: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: '#fff' }}>
      <Sequence from={0} durationInFrames={60}>
        <FadeInText text="Hello" />
      </Sequence>

      <Sequence from={60} durationInFrames={60}>
        <SlideInText text="World" direction="right" />
      </Sequence>

      <Sequence from={120} durationInFrames={90}>
        <TypewriterText text="Remotion is awesome!" />
      </Sequence>

      <Sequence from={210} durationInFrames={60}>
        <BounceText text="The End" />
      </Sequence>
    </AbsoluteFill>
  );
};

// Register composition
<Composition
  id="TextShowcase"
  component={TextShowcase}
  durationInFrames={270}
  fps={30}
  width={1920}
  height={1080}
/>
```

---

These templates provide a solid foundation for text animations. Mix and match, customize parameters, and combine with other effects to create unique animations!
