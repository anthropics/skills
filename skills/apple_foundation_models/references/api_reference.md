# API Reference

## SystemLanguageModel

The `SystemLanguageModel` class provides access to Apple's on-device language models optimized for efficiency and privacy.

### Overview

SystemLanguageModel is the main entry point for interacting with Apple's Foundation Models. It provides:
- On-device inference with no data leaving the device
- Optimized for Apple Silicon (A17 Pro and M-series chips)
- Session-based conversation management
- Built-in safety guardrails

### Initialization

```swift
import Foundation
import SystemLanguageModel

// Get the default system model
let model = try await SystemLanguageModel()

// Check if model is available
if SystemLanguageModel.isAvailable {
    let model = try await SystemLanguageModel()
} else {
    print("Model not available on this device")
}
```

### Properties

#### isAvailable
```swift
static var isAvailable: Bool { get }
```
Returns `true` if the system language model is available on the current device. Available on devices with A17 Pro or M-series chips running iOS 18.1+, macOS 15.1+, or iPadOS 18.1+.

#### sessionTokenLimit
```swift
var sessionTokenLimit: Int { get }
```
The maximum number of tokens allowed in a session, including both input and output tokens.

### Creating Sessions

#### session(with:)
```swift
func session(with guardrails: Guardrails = .automatic) async throws -> LanguageModelSession
```

Creates a new conversation session with optional safety guardrails.

**Parameters:**
- `guardrails`: The level of content filtering to apply (default: `.automatic`)

**Returns:** A `LanguageModelSession` instance for managing the conversation

**Example:**
```swift
// Create session with automatic guardrails
let session = try await model.session()

// Create session with custom guardrails
let session = try await model.session(with: .automatic)
```

### Guardrails

```swift
enum Guardrails {
    case automatic
    case disabled
}
```

Controls content filtering and safety features:
- `.automatic`: Applies Apple's default content filtering
- `.disabled`: Disables content filtering (use with caution)

---

## LanguageModelSession

Manages a conversation with the language model, maintaining context across multiple turns.

### Overview

A session maintains conversation history and manages the interaction with the model. Sessions are tied to the model's token limit and automatically handle context management.

### Creating Prompts

```swift
// Create a simple prompt
let prompt = Prompt(text: "What is Swift?")

// Create a prompt with system instructions
let prompt = Prompt {
    Instructions("You are a helpful coding assistant")
    "Explain closures in Swift"
}
```

### Generating Responses

#### respond(to:)
```swift
func respond(to prompt: Prompt) async throws -> String
```

Generates a complete response to a prompt.

**Parameters:**
- `prompt`: The input prompt

**Returns:** The complete generated response as a String

**Throws:** Errors if generation fails or content is filtered

**Example:**
```swift
let session = try await model.session()
let prompt = Prompt(text: "Explain Swift's type system")
let response = try await session.respond(to: prompt)
print(response)
```

#### streamResponse(to:)
```swift
func streamResponse(to: Prompt) -> AsyncThrowingStream<String, Error>
```

Streams the response token-by-token as it's generated.

**Parameters:**
- `prompt`: The input prompt

**Returns:** An async stream of String tokens

**Example:**
```swift
let session = try await model.session()
let prompt = Prompt(text: "Write a short story")

for try await token in session.streamResponse(to: prompt) {
    print(token, terminator: "")
}
print() // New line after complete response
```

### Guided Generation

#### respond(to:using:)
```swift
func respond<T: Generable>(to prompt: Prompt, using schema: T.Type) async throws -> T
```

Generates structured output conforming to a Swift type.

**Type Parameters:**
- `T`: A type conforming to `Generable`

**Parameters:**
- `prompt`: The input prompt
- `schema`: The type to generate

**Returns:** An instance of type `T`

**Example:**
```swift
struct Recipe: Generable {
    var title: String
    var ingredients: [String]
    var steps: [String]
}

let session = try await model.session()
let prompt = Prompt(text: "Give me a simple pasta recipe")
let recipe = try await session.respond(to: prompt, using: Recipe.self)
print(recipe.title)
```

### Tool Calling

#### respond(to:withTools:)
```swift
func respond(to prompt: Prompt, withTools tools: [Tool]) async throws -> String
```

Generates a response with access to custom tools.

**Parameters:**
- `prompt`: The input prompt
- `tools`: Array of tools the model can use

**Returns:** The generated response as a String

**Example:**
```swift
struct WeatherTool: Tool {
    static let description = "Gets current weather for a location"
    
    struct Arguments: Decodable {
        let location: String
    }
    
    func call(arguments: Arguments) async throws -> String {
        // Fetch weather data
        return "Sunny, 72°F"
    }
}

let session = try await model.session()
let prompt = Prompt(text: "What's the weather in San Francisco?")
let response = try await session.respond(to: prompt, withTools: [WeatherTool()])
```

### Session Management

Sessions automatically manage conversation history within the token limit. When the limit is approached, older messages are removed to make room for new ones.

```swift
// Sessions maintain context across multiple interactions
let session = try await model.session()

let response1 = try await session.respond(to: Prompt(text: "My name is Alice"))
let response2 = try await session.respond(to: Prompt(text: "What's my name?"))
// response2 will reference "Alice" from the conversation history
```

---

## GenerationOptions

Control how the model generates responses with temperature, sampling mode, and token limits.

### Overview

Options that control how the model generates its response to a prompt.

```swift
struct GenerationOptions {
    var sampling: SamplingMode
    var temperature: Double
    var maximumResponseTokens: Int?
}
```

### Creating Options

```swift
let options = GenerationOptions(
    sampling: .greedy,
    temperature: 0.7,
    maximumResponseTokens: 500
)

let response = try await session.respond(
    options: options,
    prompt: Prompt("Write a short story")
)
```

### Properties

**sampling** - Sampling strategy for token selection
- `.greedy` - Always pick most likely token (deterministic)
- `.topK(k: Int)` - Sample from top K most likely tokens
- `.topP(p: Double)` - Nucleus sampling (cumulative probability)

**temperature** - Influences confidence (0.0 to 1.0)
- `0.0` - Very deterministic, conservative
- `0.5` - Balanced (default)
- `1.0` - More creative, random

**maximumResponseTokens** - Limit response length
- `nil` - Use model default
- `100-2000` - Typical range

### Usage Examples

```swift
// Deterministic, factual responses
let factualOptions = GenerationOptions(
    sampling: .greedy,
    temperature: 0.0,
    maximumResponseTokens: 200
)

// Creative writing
let creativeOptions = GenerationOptions(
    sampling: .topP(p: 0.9),
    temperature: 0.8,
    maximumResponseTokens: 1000
)

// Balanced
let balancedOptions = GenerationOptions(
    sampling: .topK(k: 50),
    temperature: 0.5,
    maximumResponseTokens: 500
)
```

---

### Error Handling

```swift
do {
    let session = try await model.session()
    let response = try await session.respond(to: prompt)
} catch LanguageModelSession.GenerationError.guardrailViolation {
    // Content was filtered by safety guardrails
    print("Response blocked by guardrails")
} catch let error as SystemLanguageModelError {
    switch error {
    case .modelUnavailable:
        print("Model not available on this device")
    case .tokenLimitExceeded:
        print("Prompt exceeds token limit")
    default:
        print("Error: \(error)")
    }
}
```

**Common Errors:**
- `GenerationError.guardrailViolation` - Content filtered for safety
- `GenerationError.tokenLimitExceeded` - Too many tokens
- `GenerationError.modelUnavailable` - Model not ready
- `ToolCallError` - Tool execution failed
```
