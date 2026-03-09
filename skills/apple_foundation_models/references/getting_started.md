# Getting Started

## Foundation Models Framework Overview

Perform tasks with the on-device model that specializes in language understanding, structured output, and tool calling.

**Platforms:** iOS 26.0+, iPadOS 26.0+, Mac Catalyst 26.0+, macOS 26.0+, visionOS 26.0+

## Key Features

- **On-Device Processing**: All AI operations run locally for privacy and offline capability
- **Language Understanding**: Sophisticated natural language comprehension
- **Structured Output**: Generate Swift data structures with guided generation
- **Tool Calling**: Extend model capabilities with custom tools
- **Safety**: Built-in guardrails for sensitive content
- **Localization**: Multi-language support

## Essentials

### Generating content and performing tasks with Foundation Models
Enhance the experience in your app by prompting an on-device large language model.

### Improving the safety of generative model output
Create generative experiences that appropriately handle sensitive inputs and respect people.

### Supporting languages and locales with Foundation Models
Generate content in the language people prefer when they interact with your app.

### Adding intelligent app features with generative models
Build robust apps with guided generation and tool calling by adopting the Foundation Models framework.

## SystemLanguageModel.Availability

The availability status for a specific system language model.

**Possible States:**
- Model is ready and available
- Model is being downloaded
- Model is not available on this device
- System is preparing the model

## Checking Model Availability

Before using the model, always check availability:

```swift
let model = SystemLanguageModel.default
if model.isAvailable {
    // Ready to use
} else {
    // Check detailed availability status
    switch model.availability {
    case .available:
        // Model ready
    case .downloading:
        // Model being downloaded
    case .unavailable:
        // Not available on this device
    }
}
```

## Supported Languages

```swift
let model = SystemLanguageModel.default
let supportedLanguages = model.supportedLanguages

// Check if a specific locale is supported
if model.supportsLocale(Locale.current) {
    // Use user's preferred language
}
```

## Model Capabilities

When considering features for your app, it helps to know what the on-device language model can do. The on-device model supports text generation and understanding that you can use to:

| Capability | Prompt Example |
|------------|----------------|
| **Summarize** | "Summarize this article." |
| **Extract entities** | "List the people and places mentioned in this text." |
| **Understand text** | "What happens to the dog in this story?" |
| **Refine or edit text** | "Change this story to be in second person." |
| **Classify or judge text** | "Is this text relevant to the topic 'Swift'?" |
| **Compose creative writing** | "Generate a short bedtime story about a fox." |
| **Generate tags from text** | "Provide two tags that describe the main topics of this text." |
| **Generate game dialog** | "Respond in the voice of a friendly inn keeper." |

### Capabilities to Avoid

The on-device language model **may not be suitable** for handling all requests, like:

| Capabilities to Avoid | Prompt Example |
|----------------------|----------------|
| **Do basic math** | "How many b's are there in bagel?" |
| **Create code** | "Generate a Swift navigation list." |
| **Perform logical reasoning** | "If I'm at Apple Park facing Canada, what direction is Texas?" |

The model can complete **complex generative tasks** when you use **guided generation** or **tool calling**. For more on handling complex tasks, or tasks that require extensive world-knowledge, see the Guided Generation and Tool Calling reference files.

## Checking Availability with UI

```swift
struct GenerativeView: View {
    // Create a reference to the system language model.
    private var model = SystemLanguageModel.default
    
    var body: some View {
        switch model.availability {
        case .available:
            // Show your intelligence UI
            IntelligenceFeatureView()
            
        case .unavailable(.deviceNotSupported):
            Text("This device doesn't support Foundation Models")
            
        case .unavailable(.downloading):
            ProgressView("Downloading model...")
            
        case .unavailable(.unknown):
            Text("Model status unknown")
        }
    }
}
```

## Quick Start Example

```swift
import FoundationModels

// 1. Create the model (check availability first)
let model = SystemLanguageModel.default

guard model.availability == .available else {
    print("Model not available")
    return
}

// 2. Create a session
let session = LanguageModelSession(model: model)

// 3. Send a prompt
let response = try await session.respond(
    to: Prompt("What is the capital of France?")
)

print(response)
```

## Use Cases

Foundation Models supports different use cases for specialization:

- **General**: General-purpose language understanding
- **Writing**: Content creation and editing
- **Summarization**: Text summarization tasks
- **Content Tagging**: Categorizing and organizing data with content tags
- **Custom**: Use custom adapters for specialized behavior

```swift
// Specialized for writing tasks
let writingModel = SystemLanguageModel(useCase: .writing)

// Content tagging for categorization
let contentTaggingModel = SystemLanguageModel(useCase: .contentTagging)
```

### Content Tagging Use Case

A content tagging model produces a list of categorizing tags based on the input text you provide. When you prompt the content tagging model, it produces a tag that uses **one to a few lowercase words**.

**Example: Automatic Hashtag Generation**

```swift
let contentTaggingModel = SystemLanguageModel(useCase: .contentTagging)

.task {
    if !contentTaggingModel.isAvailable { return }
    do {
        let session = LanguageModelSession(model: contentTaggingModel)
        let stream = session.streamResponse(
            to: landmark.description,
            generating: TaggingResponse.self,
            options: GenerationOptions(sampling: .greedy)
        )
        for try await newTags in stream {
            generatedTags = newTags.content
        }
    } catch {
        print("Error: \(error.localizedDescription)")
    }
}
```

For example, for a landmark description about Yosemite, the content tagging model might generate tags like: `#nature`, `#hiking`, `#scenic`, `#wilderness`.
