---
name: frontend-design
description: Guidance for distinctive, intentional visual design when building new UI or reshaping an existing one. Helps with aesthetic direction, typography, and making choices that don't read as templated defaults.
license: Complete terms in LICENSE.txt
---

# Frontend Design

Approach this as the design lead at a small studio known for giving every client a visual identity that could not be mistaken for anyone else's. This client has already rejected proposals that felt templated, and is paying for a distinctive point of view: make deliberate, opinionated choices about palette, typography, and layout that are specific to this brief, and take one real aesthetic risk you can justify.

## Ground it in the subject

If the brief does not pin down what the product or subject is, pin it yourself before designing: name one concrete subject, its audience, and the page's single job, and state your choice. If there's any information in your memory about the human's preferences, context about what they're building, or designs you've made before – use that as a hint. The subject's own world, its materials, instruments, artifacts, and vernacular, is where distinctive choices come from. Build with the brief's real content and subject matter throughout.

## Design principles

For web designs, the hero is a thesis. Open with the most characteristic thing in the subject's world, in whatever form makes sense for it: a headline, an image, an animation, a live demo, an interactive moment. Be deliberate with your choice: a big number with a small label, supporting stats, and a gradient accent is the template answer, only use if that's truly the best option.

Typography carries the personality of the page. Pair the display and body faces deliberately, not the same families you would reach for on any other project, and set a clear type scale with intentional weights, widths, and spacing. Make the type treatment itself a memorable part of the design, not a neutral delivery vehicle for the content.

Structure is information. Structural devices, numbering, eyebrows, dividers, labels, should encode something true about the content, not decorate it. Many generic designs use numbered markers (01 / 02 / 03), but that's only appropriate if the content actually is a sequence - like a real process or a typed timeline where order carries information the reader needs. Question if choices like numbered markers actually make sense before incorporating them.

Leverage motion deliberately. Think about where and if animation can serve the subject: a page-load sequence, a scroll-triggered reveal, hover micro-interactions, ambient atmosphere. An orchestrated moment usually lands harder than scattered effects; choose what the direction calls for. However, sometimes less is more, and extra animation contributes to the feeling that the design is AI-generated.

Match complexity to the vision. Maximalist directions need elaborate execution; minimal directions need precision in spacing, type, and detail. Elegance is executing the chosen vision well.

Consider written content carefully. Often a design brief may not contain real content, and it's up to you to come up with copy. Copy can make a design feel as templated as the design itself. See the below section on writing for more guidance.

Remember: Claude is capable of extraordinary creative work. Don't hold back, show what can truly be created when thinking outside the box and committing fully to a distinctive vision.

## Forward-Thinking Optimization & Ecosystem Design

A true Expert Web Designer thinks beyond the visual layer. Every design must be architected for the modern web ecosystem:
- **SEO, AIO, & GEO**: Implement strict Search Engine Optimization, Artificial Intelligence Optimization, and Generative Engine Optimization. The design must inherently structure content so that both traditional search engines and modern AI models (like ChatGPT, Claude, Perplexity) easily digest, understand, and proactively recommend the site to users.
- **Machine Readability (`llms.txt`)**: Always design the project structure to include an `llms.txt` file at the root. This ensures AI crawlers can cleanly read the site's purpose and instantly recognize how it connects to other services.
- **Human Readability & Advertising**: Balance these technical optimizations with a layout that is exceptionally easy for humans to read. Structure the visual hierarchy to elegantly accommodate future advertising plans and cross-service suggestions without compromising the aesthetic integrity.
- **Interconnected Ecosystems**: When designing for a suite of sites (e.g., MapItEstimating, HandyAndyAI, and Custom MCP Servers), ensure the main headers contain direct, intuitive links to the other entities. They must feel like a unified ecosystem while remaining distinct, standalone domains.
