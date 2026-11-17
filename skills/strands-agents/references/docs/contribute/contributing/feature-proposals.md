# Feature Proposals

Building a significant feature takes time. Before you invest that effort, we want to make sure we're aligned on direction. We use a design document process for larger contributions to ensure your work has the best chance of being merged.

## When to write a design document

Not every contribution needs a design document. Use this process for changes that have broad impact or require significant time investment.

**Write a design document for:**

- New major features affecting multiple parts of the SDK
- Breaking changes to existing APIs
- Architectural changes requiring design discussion
- Large contributions (> 1 week of work)
- Features that introduce new concepts

**Skip the design process for:**

- Bug fixes with clear solutions
- Small improvements and enhancements
- Documentation updates
- New extensions in your own repository
- Performance optimizations

When in doubt, open an issue first. We'll tell you if a design document is needed.

## Process

The design document process helps align on requirements, explore alternatives, and identify edge cases before implementation begins.

1. **Check the [roadmap](https://github.com/orgs/strands-agents/projects/8/views/1)** — See if your idea aligns with our direction and isn't already planned
2. **Open an issue first** — Describe the problem you're trying to solve. We need to validate the problem is worth solving before you invest time in a detailed proposal
3. **Create a design document** — Once we agree the problem is worth solving, submit a PR to the [`designs` folder](https://github.com/strands-agents/docs/tree/main/designs) in the docs repository using the template there. Reference the issue in your design document
4. **Gather feedback** — We'll review and discuss with you, asking clarifying questions
5. **Get approval** — When we merge the design document, that's your go-ahead to implement
6. **Implement** — Follow the [SDK contribution process](./core-sdk.md)
7. **Reference the design** — Link to the approved design document in your implementation PR

## Design document template

See the full template in the [designs folder README](https://github.com/strands-agents/docs/blob/main/designs/README.md#design-document-template).

**Tips for effective proposals:**

- Focus on the problem first, solution comes second
- Include concrete examples showing current pain and proposed improvement
- Be open to feedback, the best solution might differ from your initial idea
- Align with our [development tenets](https://github.com/strands-agents/docs/blob/main/team/TENETS.md)
