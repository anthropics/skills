---
name: Apple Foundation Models
description: Use this skill when working with Apple's Foundation Models framework for on-device AI and LLM capabilities in iOS/macOS apps
version: 1.0.0
---

# Apple Foundation Models Skill

## When to Use This Skill

Use this skill when you need help with:

- **On-device AI**: Building iOS/macOS apps with on-device language models
- **SystemLanguageModel**: Working with Apple's on-device LLM API
- **Guided Generation**: Generating structured Swift types from prompts
- **Tool Calling**: Extending model capabilities with custom tools
- **Prompting**: Crafting effective prompts for on-device models
- **Safety**: Implementing guardrails and handling sensitive content
- **Localization**: Supporting multilingual AI features

This skill covers iOS 26.0+, iPadOS 26.0+, macOS 26.0+, and visionOS 26.0+.

## Description
Use this skill when working with Apple's Foundation Models framework for on-device AI and LLM capabilities in iOS/macOS apps. Covers SystemLanguageModel, LanguageModelSession, guided generation, tool calling, and prompting patterns.

## Quick Reference

### Core Components

### Advanced
- `Transcript`
- `Transcript.Entry`
- `Transcript.Response`
- `Transcript.ResponseFormat`
- `Transcript.Segment`
- `Transcript.StructuredSegment`

### Api Reference
- `FoundationModels`
- `GenerationID`
- `SystemLanguageModel`
- `SystemLanguageModel.Adapter`
- `SystemLanguageModel.Guardrails`
- `SystemLanguageModel.UseCase`

### Getting Started
- `SystemLanguageModel.Availability`

### Guided Generation
- `DynamicGenerationSchema`
- `Generable`
- `GenerationGuide`
- `GenerationSchema`
- `Guide`

### Localization
- `LanguageModelFeedback`

### Prompting
- `Instructions`
- `InstructionsBuilder`
- `InstructionsRepresentable`
- `LanguageModelSession`
- `LanguageModelSession.GenerationError`
- `LanguageModelSession.ToolCallError`
- `Prompt`
- `PromptBuilder`
- `PromptRepresentable`
- `Transcript.Instructions`
- `Transcript.Prompt`

### Tool Calling
- `Tool`


## Key Concepts

### Platform Support
- iOS 26.0+
- iPadOS 26.0+
- macOS 26.0+
- Mac Catalyst 26.0+
- visionOS 26.0+

### On-Device AI
All models run entirely on-device, ensuring privacy and offline capability.

## Usage Guidelines

1. Check model availability before use
2. Define clear instructions for the model's behavior
3. Use guided generation for structured outputs
4. Implement tool calling for dynamic capabilities
5. Handle errors appropriately

## Navigation

See the `references/` directory for detailed API documentation organized by category:
- `references/advanced.md` - Advanced
- `references/api_reference.md` - Api Reference
- `references/getting_started.md` - Getting Started
- `references/guided_generation.md` - Guided Generation
- `references/localization.md` - Localization
- `references/prompting.md` - Prompting
- `references/tool_calling.md` - Tool Calling


## Best Practices

- **Prompting**: Be specific and clear in your prompts
- **Instructions**: Define the model's behavior upfront
- **Safety**: Enable guardrails for sensitive content
- **Localization**: Check supported languages for your use case
- **Performance**: Use prewarm() for better response times
- **Streaming**: Use streamResponse() for real-time user feedback

## Common Patterns

### Basic Session
```swift
let model = SystemLanguageModel(useCase: .general)
let session = LanguageModelSession(model: model)
let response = try await session.respond(to: Prompt("Your question"))
```

### Guided Generation
```swift
struct Recipe: Generable {
    let title: String
    let ingredients: [String]
}

let recipe = try await session.respond(
    generating: Recipe.self,
    prompt: Prompt("Create a pasta recipe")
)
```

### Tool Calling
```swift
struct WeatherTool: Tool {
    func call(arguments: String) async throws -> String {
        // Fetch weather data
    }
}

let session = LanguageModelSession(
    model: model,
    tools: [WeatherTool()]
)
```

## Reference Documentation

For complete API details, see the categorized documentation in the `references/` directory.
