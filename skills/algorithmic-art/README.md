# Algorithmic Art

A skill for creating generative art, data visualizations, and interactive visual experiences using computational algorithms and code-based art techniques.

## Quick Start

**Use this skill when:**
- Creating generative/procedural art
- Building data visualizations
- Designing interactive visual experiences
- Exploring algorithms visually
- Building creative coding projects
- You want to turn ideas into visual code

## What This Skill Covers

### Generative Art
- Procedurally generated visual patterns
- Mathematical visualizations (fractals, chaos, etc.)
- Algorithmic drawing and composition
- Creative use of randomness and iteration

### Data Visualization
- Visual representation of data
- Interactive charts and graphs
- Information design using code
- Real-time data visualization

### Creative Coding
- Code-based art (p5.js, Processing, Three.js)
- Shader-based visual effects
- Animation and motion
- Interactive installations and experiences

### Artistic Algorithms
- Computational geometry
- Cellular automata and emergent behavior
- Noise and randomness in art
- Physics-based simulations
- Color and palette generation

## Supported Platforms & Libraries

### JavaScript/p5.js
- Easiest for beginners
- Great for visual sketches and prototypes
- Web-based (runs in browser)
- Large community and examples

### Processing/Python
- Educational and artistic focus
- Desktop applications
- Fine-grained control
- Academic visualization

### Three.js (WebGL)
- 3D graphics
- Real-time performance
- Modern browser support
- Complex interactive experiences

### Shaders (GLSL)
- GPU-accelerated graphics
- Visual effects and distortions
- Real-time performance
- Advanced users

## How to Use This Skill

1. **Read SKILL.md** for comprehensive guidance (404 lines)
2. **Check references/**:
   - `philosophy-guide.md` — creating algorithmic philosophies
3. **Start with a concept** — what visual do you want to create?
4. **Choose a platform** — p5.js for web, Processing for desktop, Three.js for 3D
5. **Build iteratively** — start simple, add complexity
6. **Share and iterate** — get feedback, evolve the work

## Quick Concepts

### Algorithmic Philosophy
Every generative art piece should have a clear "philosophy" — the core idea or principle that drives it:

❌ **Weak**: "Random shapes"  
✅ **Strong**: "Concentric circles grown by a diffusion-limited aggregation algorithm, with growth speed modulated by sine waves"

The philosophy:
- Guides what the code does
- Determines parameters and variations
- Explains artistic intent
- Helps others understand or remix your work

See `references/philosophy-guide.md` for detailed guidance.

### Key Principles

**Intentionality**: Every algorithm choice should serve the visual concept

**Variation**: Parameterize your code so you can explore variations easily

**Aesthetics**: Write code that makes beautiful things, not just correct things

**Efficiency**: Use appropriate data structures; generative art can be computationally expensive

**Control**: Balance randomness with constraints; chaos needs structure

## Common Patterns

### Pattern: Randomness with Constraints
```
Start with noise or random seed
Apply rules or transformations
Constrain to artistic bounds
Iterate and refine
```

### Pattern: Iterative Generation
```
Initialize with simple shape
Apply transformation rules
Repeat many times
Layer results with blending
```

### Pattern: Interactive Exploration
```
Set up parameter space
Allow user input to explore
Visualize parameter effects
Save interesting variations
```

## Getting Started: Three Approaches

### Approach 1: Start with Code (For Programmers)
1. Pick a library (p5.js, Three.js, etc.)
2. Read SKILL.md for concepts
3. Code a simple algorithm
4. Iterate on visual output
5. Refine philosophy and parameters

### Approach 2: Start with Concept (For Artists)
1. Describe visual concept in words
2. Read `philosophy-guide.md`
3. Collaborate with Claude to turn concept into algorithm
4. Claude writes code
5. Iterate on both concept and code

### Approach 3: Remix Existing Work
1. Find interesting algorithmic art
2. Understand the underlying algorithm
3. Modify parameters or add variations
4. Create new artwork by tweaking existing philosophy

## Workflow

1. **Concept**: Define what you want to create
2. **Philosophy**: Articulate the core algorithm/idea
3. **Prototype**: Build a minimal working version
4. **Visualize**: Display and evaluate results
5. **Iterate**: Adjust parameters and algorithm
6. **Refine**: Polish aesthetics and add sophistication
7. **Share**: Document and share with others

## Structure of This Skill

```
algorithmic-art/
├── SKILL.md                    # Core skill (404 lines)
├── README.md                   # This file
├── LICENSE.txt                 # Apache 2.0 license
├── references/
│   └── philosophy-guide.md     # Creating algorithmic philosophies
└── scripts/
    ├── template-p5.js          # p5.js starter template
    ├── template-three.js       # Three.js starter template
    └── example-*.js            # Example implementations
```

## Quick Reference: When to Use What

| Need | Use | Library |
|---|---|---|
| Simple 2D sketches | p5.js | JavaScript |
| Static generative images | Processing | Python or Java |
| Interactive web experience | p5.js + DOM | JavaScript |
| 3D visualization | Three.js | JavaScript |
| Real-time animation | Three.js or Shader | JavaScript/GLSL |
| Complex data viz | D3.js | JavaScript |
| Mathematical exploration | Processing | Python |
| Mobile-friendly | p5.js | JavaScript |
| High performance | WebGL/Shaders | GLSL |

## Tips for Success

**Do:**
- ✅ Start with clear artistic intent
- ✅ Use parameters to explore variations
- ✅ Build simple algorithms first, add complexity
- ✅ Test across different seeds/random states
- ✅ Document your philosophy
- ✅ Iterate on both code and aesthetics
- ✅ Share work and get feedback

**Don't:**
- ❌ Treat it as pure programming (it's art)
- ❌ Ignore the mathematics (understand what you're doing)
- ❌ Hardcode values (parameterize everything)
- ❌ Skip the aesthetic refinement (first version rarely looks great)
- ❌ Forget to save variations (they're part of the work)
- ❌ Make it too simple (exploration is half the fun)

## Common Challenges

| Challenge | Solution |
|---|---|
| Doesn't look artistic | Refine parameters; add constraints; simplify algorithm |
| Too slow/laggy | Optimize algorithm; reduce resolution; use appropriate data structures |
| Can't replicate results | Use seeds; save parameter sets; document randomness |
| Algorithm too complex | Break into smaller components; visualize intermediate steps |
| Lost artistic intent | Revisit philosophy; clarify what the algorithm expresses |

## Production Checklist

Before sharing algorithmic art:
- [ ] Clear description of the algorithm
- [ ] Documented philosophy/intent
- [ ] Source code included (or explanation)
- [ ] Parameter ranges documented
- [ ] Seeds/reproducibility handled
- [ ] Works across different environments
- [ ] Attribution and license clear
- [ ] Examples or documentation for others to understand

## Related Skills

- **canvas-design**: For visual design and composition
- **theme-factory**: For color and aesthetic systems
- **web-artifacts-builder**: For interactive web-based art
- **skill-creator**: For documenting algorithmic art approaches

## Resources

### Learning Resources
- **p5.js**: https://p5js.org/ (interactive coding)
- **Processing**: https://processing.org/ (visual programming language)
- **Three.js**: https://threejs.org/ (3D graphics)
- **Shader Art**: https://www.shadertoy.com/ (shader examples)

### Inspiration
- Generative Art communities
- Creative coding networks
- Math visualization sites
- Data art galleries

## For Contributors

### Adding New Algorithmic Patterns
1. Document philosophy clearly
2. Provide working code example
3. Include parameter guidance
4. Add to `philosophy-guide.md` if new type
5. Create template in `scripts/`

### Sharing Algorithmic Art
1. Document the algorithm
2. Save parameter sets
3. Include source code
4. Explain artistic intent
5. Make it remixable

---

**Last Updated**: August 2026  
**License**: Apache 2.0  
**Repository**: anthropics/skills

**Getting Started**: 
1. Read SKILL.md for overview
2. Check `references/philosophy-guide.md` for algorithm definition
3. Explore `scripts/` for templates and examples
4. Start coding your artwork
