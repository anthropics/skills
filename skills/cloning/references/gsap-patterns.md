# GSAP Animation Patterns Reference

Ready-to-use GSAP + ScrollTrigger code templates for React/Next.js.
When the extraction detects GSAP on the original site, inject these patterns into the Gemini prompt.

## Setup (required in every GSAP component)

```tsx
"use client";
import { useEffect, useRef } from "react";
import { gsap } from "gsap";
import { ScrollTrigger } from "gsap/ScrollTrigger";

if (typeof window !== "undefined") {
  gsap.registerPlugin(ScrollTrigger);
}
```

## Pattern 1: Word-by-Word Scroll Reveal (Manifesto/Statement sections)

Use when: A block of text where individual words progressively highlight/reveal as the user scrolls.

```tsx
export default function ScrollRevealText({ children }: { children: string }) {
  const containerRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (!containerRef.current) return;

    const words = containerRef.current.querySelectorAll(".word");

    const ctx = gsap.context(() => {
      gsap.fromTo(
        words,
        { opacity: 0.15, y: 0 },
        {
          opacity: 1,
          y: 0,
          stagger: 0.02,
          ease: "none",
          scrollTrigger: {
            trigger: containerRef.current,
            start: "top 80%",
            end: "bottom 30%",
            scrub: 0.5,
          },
        }
      );
    }, containerRef);

    return () => ctx.revert();
  }, []);

  const words = children.split(/\s+/);

  return (
    <div ref={containerRef} className="leading-relaxed">
      {words.map((word, i) => (
        <span key={i} className="word inline-block mr-[0.3em]">
          {word}
        </span>
      ))}
    </div>
  );
}
```

**How to identify this pattern:**
- Phase 6 extraction shows scroll-linked opacity changes on many sibling elements
- The original has a text block where words are individual `<span>` elements
- Scroll position controls which words are highlighted vs dimmed

## Pattern 2: Auto-Cycling Tabs with Progress Bar

Use when: A tabbed interface where tabs automatically advance every N seconds, with a progress bar showing time remaining.

```tsx
export default function AutoTabs({ tabs }: { tabs: TabData[] }) {
  const [activeIndex, setActiveIndex] = useState(0);
  const [progress, setProgress] = useState(0);
  const progressRef = useRef<gsap.core.Tween | null>(null);
  const DURATION = 6; // seconds per tab

  const startTimer = useCallback((index: number) => {
    if (progressRef.current) progressRef.current.kill();
    setProgress(0);

    progressRef.current = gsap.to(
      { value: 0 },
      {
        value: 100,
        duration: DURATION,
        ease: "none",
        onUpdate: function () {
          setProgress(this.targets()[0].value);
        },
        onComplete: () => {
          setActiveIndex((index + 1) % tabs.length);
        },
      }
    );
  }, [tabs.length]);

  useEffect(() => {
    startTimer(activeIndex);
    return () => progressRef.current?.kill();
  }, [activeIndex, startTimer]);

  return (
    <div>
      {/* Tab buttons with progress bars */}
      <div className="flex gap-4">
        {tabs.map((tab, i) => (
          <button
            key={i}
            onClick={() => { setActiveIndex(i); startTimer(i); }}
            className="flex-1 text-left"
          >
            <h3 className={i === activeIndex ? "font-bold" : "opacity-50"}>
              {tab.title}
            </h3>
            <p className="text-sm opacity-70">{tab.description}</p>
            {/* Progress bar */}
            <div className="h-1 bg-gray-200 mt-2 rounded-full overflow-hidden">
              <div
                className="h-full bg-current rounded-full transition-none"
                style={{ width: i === activeIndex ? `${progress}%` : "0%" }}
              />
            </div>
          </button>
        ))}
      </div>

      {/* Tab content */}
      <div className="mt-8">
        <Image
          src={tabs[activeIndex].image}
          alt={tabs[activeIndex].title}
          width={800}
          height={450}
          className="w-full rounded-lg transition-opacity duration-500"
        />
      </div>
    </div>
  );
}
```

**How to identify this pattern:**
- Phase 0.5 detects tab elements with auto-cycling behavior
- Multiple panels with a timer/progress indicator
- Tabs switch automatically without user interaction

## Pattern 3: Sticky Scroll Timeline / Process Steps

Use when: A vertical timeline where the sidebar stays sticky while content scrolls, with the active step updating based on scroll position.

```tsx
export default function StickyTimeline({ steps }: { steps: StepData[] }) {
  const [activeIndex, setActiveIndex] = useState(0);
  const sectionRef = useRef<HTMLDivElement>(null);
  const stepRefs = useRef<(HTMLDivElement | null)[]>([]);

  useEffect(() => {
    if (!sectionRef.current) return;

    const ctx = gsap.context(() => {
      stepRefs.current.forEach((stepEl, i) => {
        if (!stepEl) return;
        ScrollTrigger.create({
          trigger: stepEl,
          start: "top 55%",
          end: "bottom 45%",
          onEnter: () => setActiveIndex(i),
          onEnterBack: () => setActiveIndex(i),
        });
      });
    }, sectionRef);

    return () => ctx.revert();
  }, []);

  return (
    <section ref={sectionRef} className="flex gap-16 max-w-[1200px] mx-auto py-20 px-6">
      {/* Sticky sidebar */}
      <div className="hidden md:block w-48 shrink-0">
        <div className="sticky top-32 flex flex-col gap-8">
          {/* Vertical line */}
          <div className="absolute left-3 top-0 bottom-0 w-px bg-gray-200" />
          {steps.map((step, i) => (
            <button
              key={step.label}
              onClick={() => stepRefs.current[i]?.scrollIntoView({ behavior: "smooth", block: "center" })}
              className={`flex items-center gap-4 relative z-10 transition-opacity duration-300 ${
                i === activeIndex ? "opacity-100" : "opacity-30"
              }`}
            >
              <div
                className="w-6 h-6 rounded-full border-4 border-white transition-transform duration-300"
                style={{
                  backgroundColor: step.color,
                  transform: i === activeIndex ? "scale(1.5)" : "scale(1)",
                }}
              />
              <span className="text-sm font-bold">{step.label}</span>
            </button>
          ))}
        </div>
      </div>

      {/* Scrolling content */}
      <div className="flex-1 flex flex-col gap-32">
        {steps.map((step, i) => (
          <div key={step.label} ref={(el) => { stepRefs.current[i] = el; }}>
            <Image src={step.image} alt={step.label} width={800} height={450}
              className="w-full rounded-lg" unoptimized />
            <p className="mt-6 text-xl leading-relaxed">
              <strong>{step.title}</strong> {step.description}
            </p>
          </div>
        ))}
      </div>
    </section>
  );
}
```

**How to identify this pattern:**
- Phase 4 detects a progress/steps component
- Phase 3 shows a sticky positioned sidebar
- Multiple content panels that scroll while navigation stays fixed

## Pattern 4: Entrance Fade + Slide with Stagger

Use when: Multiple elements appear with a cascading animation as they enter the viewport.

```tsx
export default function StaggerReveal({ children }: { children: React.ReactNode }) {
  const ref = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (!ref.current) return;

    const items = ref.current.querySelectorAll(".stagger-item");

    const ctx = gsap.context(() => {
      gsap.fromTo(
        items,
        { opacity: 0, y: 40 },
        {
          opacity: 1,
          y: 0,
          duration: 0.8,
          stagger: 0.1,
          ease: "power2.out",
          scrollTrigger: {
            trigger: ref.current,
            start: "top 80%",
            once: true,
          },
        }
      );
    }, ref);

    return () => ctx.revert();
  }, []);

  return <div ref={ref}>{children}</div>;
}
```

## Pattern 5: Horizontal Scroll Section (Pinned)

Use when: A section pins to the viewport while content scrolls horizontally.

```tsx
export default function HorizontalScroll({ panels }: { panels: PanelData[] }) {
  const containerRef = useRef<HTMLDivElement>(null);
  const panelsRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (!containerRef.current || !panelsRef.current) return;

    const totalWidth = panelsRef.current.scrollWidth - window.innerWidth;

    const ctx = gsap.context(() => {
      gsap.to(panelsRef.current, {
        x: -totalWidth,
        ease: "none",
        scrollTrigger: {
          trigger: containerRef.current,
          start: "top top",
          end: `+=${totalWidth}`,
          scrub: 1,
          pin: true,
        },
      });
    }, containerRef);

    return () => ctx.revert();
  }, []);

  return (
    <section ref={containerRef} className="overflow-hidden">
      <div ref={panelsRef} className="flex w-max">
        {panels.map((panel, i) => (
          <div key={i} className="w-screen h-screen flex items-center justify-center px-20">
            {panel.content}
          </div>
        ))}
      </div>
    </section>
  );
}
```

## Package.json Requirement

When ANY of these patterns are used, ensure:
```json
{
  "dependencies": {
    "gsap": "^3.12.0"
  }
}
```

And in the component that uses GSAP:
```tsx
// This MUST be at the top of every GSAP component
if (typeof window !== "undefined") {
  gsap.registerPlugin(ScrollTrigger);
}
```

## When NOT to Use GSAP

- Simple fade-in on viewport entry -> use CSS @keyframes + IntersectionObserver
- Hover transitions -> use CSS :hover
- Continuous loops (spinners, pulsing) -> use CSS @keyframes infinite
- CSS-only sites (Phase 0 detects NO animation library) -> do NOT add GSAP
