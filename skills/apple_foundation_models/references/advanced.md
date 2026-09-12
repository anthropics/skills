# Advanced

## Custom Adapters

### Loading and Using Custom Adapters

Foundation Models supports custom adapters that specialize the base model for specific use cases without retraining the entire model from scratch. Adapters are trained by you to modify the model's behavior while maintaining its core capabilities.

### Training an Adapter

**Before you can load a custom adapter, you first need to train one with an adapter training toolkit.**

The toolkit uses **Python and PyTorch** and requires familiarity with training machine-learning models. After training, use the toolkit to export the adapter in a format compatible with Foundation Models.

**Requirements:**
- Python 3.8+
- PyTorch
- Training data specific to your use case
- Familiarity with ML model training

### Deploying Adapters

**Important:** Adapter files are large (**160 MB or more**), so **don't bundle them in your app**.

**Deployment Options:**
1. **App Store Connect** - Host via on-demand resources
2. **Your Server** - Download on-demand based on user needs
3. **Local Development** - Load from file URL during testing

### SystemLanguageModel.Adapter

Load an adapter from a local file URL:

```swift
// The absolute path to your adapter
let localURL = URL(filePath: "absolute/path/to/my_adapter.fmadapter")

// Initialize the adapter by using the local URL
let adapter = try SystemLanguageModel.Adapter(fileURL: localURL)

// Create model instance with the adapter
let customAdapterModel = SystemLanguageModel(adapter: adapter)

// Create a session and prompt the model
let session = LanguageModelSession(model: customAdapterModel)
let response = try await session.respond(to: "Your prompt here")
```

### Requirements

To use custom adapters:

1. **Entitlement Required**: Add `com.apple.developer.foundation-model-adapter` capability
2. **Train Adapter**: Use Apple's adapter training toolkit (Python/PyTorch)
3. **Export Adapter**: Convert to `.fmadapter` format
4. **Deploy Adapter**: Host remotely (App Store or your server)
5. **Download On-Demand**: Fetch when needed (don't bundle in app)

### Checking Adapter Availability

```swift
guard SystemLanguageModel.isAvailable else {
    print("Model not available on this device")
    return
}

// Check if adapter file exists
let adapterURL = getAdapterURL() // Your method to get/download adapter
guard FileManager.default.fileExists(atPath: adapterURL.path) else {
    print("Adapter file not found")
    return
}

// Initialize with adapter
do {
    let adapter = try SystemLanguageModel.Adapter(fileURL: adapterURL)
    let model = SystemLanguageModel(adapter: adapter)
    let session = LanguageModelSession(model: model)
} catch {
    print("Failed to load adapter: \(error)")
}
```

### Use Cases for Custom Adapters

- **Domain-Specific Language**: Medical, legal, or technical terminology
- **Brand Voice**: Consistent tone and style for your brand
- **Specialized Tasks**: Custom classification or extraction
- **Language Variants**: Dialects or industry-specific language

---

## Transcript Management

### Transcript Struct

The `Transcript` struct represents a linear history of interactions with the model.

**Purpose:**
- Save and restore conversation history
- Export conversations
- Analyze interaction patterns
- Implement conversation replay

### Creating Transcripts

```swift
// Session automatically maintains a transcript
let session = LanguageModelSession(model: model)

// Access the transcript
let currentTranscript = session.transcript

// Save transcript for later
let transcriptData = try JSONEncoder().encode(currentTranscript)
UserDefaults.standard.set(transcriptData, forKey: "savedTranscript")
```

### Restoring from Transcript

```swift
// Load saved transcript
guard let transcriptData = UserDefaults.standard.data(forKey: "savedTranscript"),
      let transcript = try? JSONDecoder().decode(Transcript.self, from: transcriptData) else {
    return
}

// Create session from transcript
let session = LanguageModelSession(
    model: model,
    tools: [],
    transcript: transcript
)

// Continue conversation from where it left off
let response = try await session.respond(to: Prompt("Continue our discussion"))
```

### Transcript Structure

```swift
struct Transcript: Codable {
    let entries: [Entry]
    
    struct Entry: Codable {
        let timestamp: Date
        let segment: Segment
    }
    
    enum Segment: Codable {
        case instructions(Instructions)
        case prompt(Prompt)
        case response(Response)
        case toolCall(ToolCall)
        case toolResult(ToolResult)
    }
}
```

### Analyzing Transcripts

```swift
func analyzeConversation(_ transcript: Transcript) {
    let promptCount = transcript.entries.filter { entry in
        if case .prompt = entry.segment { return true }
        return false
    }.count
    
    let responseCount = transcript.entries.filter { entry in
        if case .response = entry.segment { return true }
        return false
    }.count
    
    let toolCallCount = transcript.entries.filter { entry in
        if case .toolCall = entry.segment { return true }
        return false
    }.count
    
    print("Conversation stats:")
    print("- Prompts: \(promptCount)")
    print("- Responses: \(responseCount)")
    print("- Tool calls: \(toolCallCount)")
}
```

---

## LanguageModelFeedback

### Overview

The `LanguageModelFeedback` struct provides a way to log issues and provide feedback about model responses. This helps improve the model over time and can be attached to Feedback Assistant reports.

### Recording Feedback

```swift
// After receiving a response
let response = try await session.respond(to: prompt)

// If the response has issues, log feedback
let feedback = try await session.logFeedbackAttachment(
    sentiment: .negative,
    issues: [.inaccurate, .unhelpful],
    desiredOutput: "The model should have provided more specific Swift code examples"
)

// Attach to Feedback Assistant
// (Feedback Assistant integration code)
```

### LanguageModelFeedback.Sentiment

Represents your overall sentiment about the response:

```swift
enum Sentiment {
    case positive    // Response was helpful and accurate
    case neutral     // Response was acceptable
    case negative    // Response had significant issues
}
```

### LanguageModelFeedback.Issue

Specific issues with the model's response:

```swift
enum Issue {
    case inaccurate           // Factually incorrect information
    case unhelpful            // Didn't address the question
    case inappropriate        // Violated content policies
    case incomplete           // Missing important information
    case irrelevant           // Off-topic response
    case formatIncorrect      // Didn't follow requested format
    case toolCallFailed       // Tool calling didn't work as expected
}
```

### Complete Feedback Example

```swift
func handleResponse(prompt: Prompt, response: String, session: LanguageModelSession) async {
    // Evaluate response quality
    let isGoodResponse = evaluateResponse(response)
    
    if !isGoodResponse {
        do {
            let feedback = try await session.logFeedbackAttachment(
                sentiment: .negative,
                issues: [.inaccurate, .incomplete],
                desiredOutput: """
                Expected a comprehensive answer with:
                1. Clear explanation
                2. Code examples
                3. Best practices
                """
            )
            
            // Log for analytics
            print("Feedback logged: \(feedback)")
            
            // Optionally show user feedback UI
            await showFeedbackConfirmation()
        } catch {
            print("Failed to log feedback: \(error)")
        }
    }
}

func evaluateResponse(_ response: String) -> Bool {
    // Your evaluation logic
    return response.count > 50 && !response.contains("I don't know")
}
```

### Automatic Feedback Collection

```swift
class FeedbackCollector {
    func collectFeedbackAutomatically(
        session: LanguageModelSession,
        prompt: Prompt,
        response: String
    ) async throws {
        // Analyze response quality
        let hasCodeExamples = response.contains("```")
        let isSubstantive = response.count > 100
        let hasStructure = response.contains("\n\n")
        
        let sentiment: LanguageModelFeedback.Sentiment
        var issues: [LanguageModelFeedback.Issue] = []
        
        if hasCodeExamples && isSubstantive && hasStructure {
            sentiment = .positive
        } else {
            sentiment = .neutral
            
            if !hasCodeExamples {
                issues.append(.incomplete)
            }
            if !isSubstantive {
                issues.append(.unhelpful)
            }
        }
        
        if !issues.isEmpty {
            _ = try await session.logFeedbackAttachment(
                sentiment: sentiment,
                issues: issues,
                desiredOutput: "More comprehensive response with examples"
            )
        }
    }
}
```

### User-Initiated Feedback

```swift
struct FeedbackView: View {
    let session: LanguageModelSession
    let prompt: Prompt
    let response: String
    
    @State private var selectedIssues: Set<LanguageModelFeedback.Issue> = []
    @State private var desiredOutput: String = ""
    
    var body: some View {
        Form {
            Section("What went wrong?") {
                Toggle("Inaccurate", isOn: binding(for: .inaccurate))
                Toggle("Unhelpful", isOn: binding(for: .unhelpful))
                Toggle("Incomplete", isOn: binding(for: .incomplete))
                Toggle("Irrelevant", isOn: binding(for: .irrelevant))
            }
            
            Section("What did you expect?") {
                TextEditor(text: $desiredOutput)
                    .frame(height: 100)
            }
            
            Button("Submit Feedback") {
                Task {
                    try await session.logFeedbackAttachment(
                        sentiment: .negative,
                        issues: Array(selectedIssues),
                        desiredOutput: desiredOutput
                    )
                }
            }
        }
    }
    
    private func binding(for issue: LanguageModelFeedback.Issue) -> Binding<Bool> {
        Binding(
            get: { selectedIssues.contains(issue) },
            set: { isSelected in
                if isSelected {
                    selectedIssues.insert(issue)
                } else {
                    selectedIssues.remove(issue)
                }
            }
        )
    }
}
```

---

## Performance Optimization

### Prewarming Sessions

Reduce latency by preloading the model and caching prompt prefixes:

```swift
// Prewarm the session with common prefix
let session = LanguageModelSession(
    model: model,
    instructions: Instructions("You are a helpful coding assistant")
)

// Prewarm with expected prompt prefix
try await session.prewarm(promptPrefix: "Explain how to use ")

// Subsequent prompts with this prefix will be faster
let response = try await session.respond(
    to: Prompt("Explain how to use async/await in Swift")
)
```

### Session Reuse

```swift
class ConversationManager {
    private var cachedSession: LanguageModelSession?
    private let model: SystemLanguageModel
    
    init(model: SystemLanguageModel) {
        self.model = model
    }
    
    func getSession() async throws -> LanguageModelSession {
        if let session = cachedSession {
            return session
        }
        
        let session = LanguageModelSession(model: model)
        cachedSession = session
        
        // Prewarm for faster first response
        try await session.prewarm()
        
        return session
    }
    
    func resetSession() {
        cachedSession = nil
    }
}
```

---

## Best Practices

### 1. Monitor Token Usage

```swift
let session = LanguageModelSession(model: model)
print("Token limit: \(model.sessionTokenLimit)")

// Track approximate token usage
var estimatedTokens = 0
estimatedTokens += prompt.text.count / 4 // Rough estimation
estimatedTokens += response.count / 4

if estimatedTokens > model.sessionTokenLimit * 0.8 {
    // Approaching limit, consider starting new session
    print("Warning: Approaching token limit")
}
```

### 2. Handle Long Conversations

```swift
func manageLongConversation() async throws {
    var session = LanguageModelSession(model: model)
    var turnCount = 0
    
    while true {
        let userInput = await getUserInput()
        
        do {
            let response = try await session.respond(to: Prompt(userInput))
            await displayResponse(response)
            
            turnCount += 1
            
            // Reset session every 10 turns to avoid token limits
            if turnCount >= 10 {
                // Save important context
                let summary = try await session.respond(
                    to: Prompt("Summarize our conversation so far")
                )
                
                // Start fresh with summary as context
                session = LanguageModelSession(
                    model: model,
                    instructions: Instructions("Previous conversation summary: \(summary)")
                )
                turnCount = 0
            }
        } catch {
            print("Error: \(error)")
        }
    }
}
```

### 3. Graceful Degradation

```swift
func respondWithFallback(prompt: Prompt) async -> String {
    do {
        let session = try await model.session()
        return try await session.respond(to: prompt)
    } catch {
        // Fallback to simpler response
        return "I apologize, but I'm unable to process your request right now. Please try again."
    }
}
```

---

## Real-World Example: Game Character Dialog

Complete example from Apple's sample app showing dynamic game content generation with guided generation and tools.

### Character Definition

```swift
protocol Character {
    var id: UUID { get }
    var displayName: String { get }
    var firstLine: String { get }
    var persona: String { get }
}

struct Barista: Character {
    let id = UUID()
    let displayName = "Barista"
    let firstLine = "Hey there. Can you get the dream orders?"
    
    let persona = """
        Chike is the head barista at Dream Coffee, and loves serving up 
        the perfect cup of coffee to all the dreamers and creatives. 
        Chike is friendly, knowledgeable about coffee, and enjoys making 
        connections with customers.
        """
}
```

### Multi-Turn Conversation System

```swift
let instructions = """
    A multiturn conversation between a game character and the player. \
    You are \(character.displayName). Refer to \(character.displayName) in \
    the first-person (like "I" or "me"). You must respond in the voice of \
    \(character.persona).
    
    Keep your responses brief - 2-3 sentences maximum.
    Stay in character at all times.
    Reference previous conversation context when appropriate.
    """

let session = LanguageModelSession(
    model: model,
    instructions: Instructions(instructions)
)

// Player can have ongoing conversations
let response1 = try await session.respond(to: Prompt("Hello!"))
let response2 = try await session.respond(to: Prompt("What's your favorite coffee?"))
let response3 = try await session.respond(to: Prompt("Can you make me one?"))
```

### Procedurally Generated Characters

```swift
@Generable(description: "A procedurally generated customer")
struct ProceduralCustomer: Character {
    var id = UUID()
    
    @Guide(description: "A unique, creative name")
    var displayName: String
    
    @Guide(description: "Opening line that introduces their personality")
    var firstLine: String
    
    @Guide(description: "2-3 sentence personality description")
    var persona: String
    
    @Guide(description: "Their favorite type of coffee or drink")
    var favoriteDrink: String
}

// Generate unique customers dynamically
let prompt = Prompt("Create a quirky regular customer who visits this coffee shop")
let customer = try await session.respond(
    to: prompt,
    generating: ProceduralCustomer.self
)

// Each customer is unique!
print(customer.displayName) // e.g., "Luna the Dreamer"
print(customer.firstLine) // e.g., "Is it morning already? I was up all night painting..."
```

### Combining Tools with Game State

```swift
struct OrderDatabaseTool: Tool {
    let name = "checkOrderStatus"
    let description = "Checks the status of a customer's coffee order"
    
    @Generable
    struct Arguments {
        @Guide(description: "The customer's name")
        var customerName: String
    }
    
    func call(arguments: Arguments) async throws -> String {
        // Query game state
        if let order = GameState.shared.getOrder(for: arguments.customerName) {
            return "Order: \(order.drinkType), Status: \(order.status)"
        }
        return "No order found for \(arguments.customerName)"
    }
}

let session = LanguageModelSession(
    model: model,
    tools: [OrderDatabaseTool()],
    instructions: Instructions(baristaInstructions)
)

// Character can reference actual game state
let response = try await session.respond(
    to: Prompt("Is Luna's latte ready yet?")
)
// Model calls OrderDatabaseTool automatically and incorporates result
```

---

## Summary

**Advanced Features:**

1. **Custom Adapters** - Specialize the model for your domain (160MB+, deploy remotely)
2. **Transcript Management** - Save, restore, and analyze conversations
3. **Feedback System** - Improve model quality with structured feedback
4. **Performance Optimization** - Prewarming and session management
5. **Token Management** - Monitor and handle token limits
6. **Error Handling** - Graceful degradation strategies
7. **Game Content** - Dynamic dialog, procedural generation, multi-turn conversations

These advanced features enable production-ready implementations with Foundation Models, including rich interactive experiences like games, chatbots, and personalized content.
