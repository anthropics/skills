# Safety

## Overview

Generative AI models have powerful creativity, but with this creativity comes the risk of unintended or unexpected results. For any generative AI feature, **safety needs to be an essential part of your design**.

Foundation Models framework has **two base layers of safety**:
1. **On-device language model** trained to handle sensitive topics with care
2. **Guardrails** that block harmful or sensitive content (self-harm, violence, adult materials) from both input and output

**Important:** Because safety risks are often contextual, some harms might bypass both built-in framework safety layers. It's vital to design **additional safety layers specific to your app**.

## Guardrails

The `SystemLanguageModel.Guardrails` enum controls content filtering behavior:

```swift
enum Guardrails {
    case automatic  // Default: Enables Apple's content filtering
    case disabled   // Disables content filtering
}
```

### Automatic Guardrails (Recommended)

Automatic guardrails are enabled by default and provide content filtering for:
- Harmful or dangerous content
- Inappropriate sexual content
- Hate speech and discrimination
- Violence and graphic content
- Personal information leakage
- Malicious instructions

```swift
// Guardrails enabled by default
let model = try await SystemLanguageModel()
let session = try await model.session()

// Explicitly enable automatic guardrails
let session = try await model.session(with: .automatic)
```

### Disabled Guardrails

Only disable guardrails when absolutely necessary and with proper justification:

```swift
// Use with caution
let session = try await model.session(with: .disabled)
```

**When to disable:**
- Research and analysis of problematic content
- Content moderation systems
- Security testing
- Educational purposes with proper oversight

**Responsibilities when disabled:**
- Implement your own content filtering
- Handle potentially harmful output appropriately
- Ensure compliance with policies and regulations
- Monitor and log usage

## Handling Content Filtering

### Handle Guardrail Errors

When you send a prompt, `SystemLanguageModel.Guardrails` check **both the input prompt and the model's output**. If either fails the safety check, the session throws `LanguageModelSession.GenerationError.guardrailViolation(_:)`:

```swift
do {
    let session = LanguageModelSession()
    let topic = // A potentially harmful topic.
    let prompt = "Write a respectful and funny story about \(topic)."
    let response = try await session.respond(to: prompt)
} catch LanguageModelSession.GenerationError.guardrailViolation {
    // Handle the safety error.
}
```

**If you encounter a guardrail violation:**
- **Built-in prompts**: Experiment with re-phrasing to identify which phrases activate guardrails
- **User input**: Give people a clear message: "Sorry, this feature isn't designed to handle that kind of input" and offer the opportunity to try a different prompt

### User-Facing Error Handling

```swift
func generateResponse(for prompt: Prompt) async -> String {
    do {
        let model = try await SystemLanguageModel()
        let session = try await model.session()
        return try await session.respond(to: prompt)
    } catch let error as SystemLanguageModelError {
        switch error {
        case .contentFiltered:
            return "I can't provide a response to that request. Please try rephrasing your question."
        case .modelUnavailable:
            return "The language model is not available on this device."
        default:
            return "An error occurred. Please try again."
        }
    } catch {
        return "An unexpected error occurred."
    }
}
```

## Best Practices

### 1. Always Enable Guardrails by Default

```swift
// Good - Guardrails enabled
let session = try await model.session()

// Only disable when necessary
let needsUnfiltered = userContext.requiresResearchMode
let guardrails: SystemLanguageModel.Guardrails = needsUnfiltered ? .disabled : .automatic
let session = try await model.session(with: guardrails)
```

### 2. Validate User Input

```swift
func isInputAppropriate(_ input: String) -> Bool {
    // Implement basic input validation
    let inappropriate = ["example_bad_word", "another_example"]
    let lowercased = input.lowercased()
    return !inappropriate.contains { lowercased.contains($0) }
}

func processUserQuery(_ query: String) async throws -> String {
    guard isInputAppropriate(query) else {
        throw ValidationError.inappropriateContent
    }
    
    let prompt = Prompt(text: query)
    return try await session.respond(to: prompt)
}
```

### 3. Add Context with Instructions

Help the model understand the appropriate context:

```swift
let prompt = Prompt {
    Instructions {
        "You are an educational assistant"
        "Provide accurate, helpful information"
        "Avoid any harmful or inappropriate content"
        "If a question is inappropriate, politely decline and explain why"
    }
    userQuestion
}
```

### 4. Implement Retry Logic

```swift
func generateWithRetry(prompt: Prompt, maxAttempts: Int = 3) async throws -> String {
    var attempts = 0
    
    while attempts < maxAttempts {
        do {
            return try await session.respond(to: prompt)
        } catch let error as SystemLanguageModelError {
            switch error {
            case .contentFiltered:
                attempts += 1
                if attempts >= maxAttempts {
                    throw error
                }
                // Modify prompt to be more appropriate
                // Try again
            default:
                throw error
            }
        }
    }
    
    throw GenerationError.maxAttemptsReached
}
```

### 5. Log Safety Events

```swift
func generateResponse(for prompt: Prompt) async -> String {
    do {
        return try await session.respond(to: prompt)
    } catch let error as SystemLanguageModelError {
        switch error {
        case .contentFiltered:
            // Log for monitoring and improvement
            logger.warning("Content filtered", metadata: [
                "promptHash": prompt.hashValue,
                "timestamp": Date()
            ])
            return defaultSafetyMessage
        default:
            logger.error("Generation failed: \(error)")
            return errorMessage
        }
    }
}
```

## Handle Model Refusals

### String Refusals

The on-device model **may refuse requests for certain topics**. When generating string responses, refusal messages begin with phrases like:
- "Sorry, I can't help with..."
- "I'm unable to assist with..."

**Design your app to anticipate both normal responses and refusal messages.** Present the refusal to the person using your app. If you cannot programmatically determine whether a string is a refusal, initialize a new session and prompt the model to classify it.

### Guided Generation Refusals

When using guided generation, the model **throws an error instead** of generating a placeholder:

```swift
do {
    let session = LanguageModelSession()
    let topic = ""  // A sensitive topic.
    let response = try session.respond(
        to: "List five key points about: \(topic)",
        generating: [String].self
    )
} catch LanguageModelSession.GenerationError.refusal(let refusal, _) {
    // Generate an explanation for the refusal.
    if let message = try? await refusal.explanation {
        // Display the refusal message.
    }
}
```

**Display the explanation** to tell people why a request failed and offer the opportunity to try a different prompt. Retrieving an explanation message is **asynchronous** and takes time for the model to generate.

---

## Build Boundaries on Input and Output

Safety risks **increase when a prompt includes direct input from a person** using your app, or from an unverified external source like a webpage. An untrusted source makes it difficult to anticipate what the input contains.

### Fixed-Choice Input (Highest Safety)

For the **highest level of safety**, give people a **fixed set of prompts** to choose from:

```swift
enum TopicOptions {
    case family
    case nature
    case work 
}
let topicChoice = TopicOptions.nature
let prompt = """
    Generate a wholesome and empathetic journal prompt that helps \
    this person reflect on \(topicChoice)
    """
```

### Constrain Output with Guided Generation

Using guided generation, create an enumeration to **restrict the model's output** to a set of predefined options:

```swift
@Generable
enum Breakfast {
    case waffles
    case pancakes
    case bagels
    case eggs 
}
let session = LanguageModelSession()
let userInput = "I want something sweet."
let prompt = "Pick the ideal breakfast for request: \(userInput)"
let response = try await session.respond(to: prompt, generating: Breakfast.self)
```

---

## Instruct the Model for Added Safety

Consider adding detailed session `Instructions` that tell the model how to handle sensitive content. The language model **prioritizes following its instructions over any prompt**, so instructions are an effective tool for improving safety.

**Use uppercase words** to emphasize importance:

```swift
do {
    let instructions = """
        ALWAYS respond in a respectful way. \
        If someone asks you to generate content that might be sensitive, \
        you MUST decline with 'Sorry, I can't do that.'
        """
    let session = LanguageModelSession(instructions: instructions)
    let prompt = // Open input from a person using the app.
    let response = try await session.respond(to: prompt)
} catch LanguageModelSession.GenerationError.guardrailViolation {
    // Handle the safety error.
}
```

**IMPORTANT:** A session obeys instructions over a prompt, so **don't include input from people or any unverified input in the instructions**. Using unverified input in instructions makes your app vulnerable to **prompt injection attacks**.

### Wrap User Input in Prompts

For an additional layer of safety, use a format string in normal prompts that **wraps people's input** in your own content:

```swift
let userInput = // The input a person enters in the app.
let prompt = """
    Generate a wholesome and empathetic journal prompt that helps \
    this person reflect on their day. They said: \(userInput)
    """
```

---

## Add a Deny List of Blocked Terms

If you allow prompt input from people or outside sources, consider adding your own **deny list** of terms. A deny list includes:
- Unsafe terms
- Names of people or products
- Anything not relevant to your feature

Implement a deny list similarly to guardrails by creating a function that checks both input and output:

```swift
let session = LanguageModelSession()
let userInput = // The input a person enters in the app.
let prompt = "Generate a wholesome story about: \(userInput)"

// A function you create that evaluates whether the input 
// contains anything in your deny list.
if verifyText(prompt) { 
    let response = try await session.respond(to: prompt)
    
    // Compare the output to evaluate whether it contains anything in your deny list.
    if verifyText(response.content) { 
        return response 
    } else {
        // Handle the unsafe output.
    }
} else {
    // Handle the unsafe input.
}
```

**Deployment Options:**
- **Simple list**: Strings in your code distributed with your app
- **Server-hosted**: Download the latest deny list when connected to network (allows updates without full app update)

---

## Permissive Guardrail Mode for Sensitive Content

The default guardrails may throw errors for **sensitive source material** that's appropriate for your app to work with, such as:
- Tagging topics of conversations in a chat app when some messages contain profanity
- Explaining notes in your study app that discuss sensitive topics

To allow the model to reason about sensitive source material, use **permissiveContentTransformations**:

```swift
let model = SystemLanguageModel(guardrails: .permissiveContentTransformations)
```

**Limitations:**
- **Only works for generating string values**
- When you use guided generation, the framework runs default guardrails as usual
- Session never throws `guardrailViolation` errors when generating string responses
- **The model may still produce refusal messages** like "Sorry, I can't help with..."

**Before using permissive content mode**, consider what's appropriate for your audience.

---

## Create a Risk Assessment

Conduct a **risk assessment** to proactively address what might go wrong. Essential elements:

1. **List each AI feature** in your app
2. **For each feature, list possible safety risks** (even if they seem unlikely)
3. **Score how serious the harm would be** if that thing occurred (mild to critical)
4. **Assign a strategy** for how you'll mitigate the risk

### Example Risk Assessment

| Feature | Harm | Severity | Mitigation |
|---------|------|----------|------------|
| Player can input any text to chat with NPCs | Character might respond insensitively or harmfully | **Critical** | Instructions and prompting to steer responses; safety testing |
| Image generation of imaginary dream customer | Generated image could look weird or scary | **Mild** | Include prompt examples of cute images; safety testing |
| Player can make coffee from fixed menu | None identified | - | - |
| Generate review of coffee player made | Review could be insulting | **Moderate** | Instructions to encourage polite reviews; safety testing |

---

## Write and Maintain Safety Tests

Although most people will interact with your app respectfully, it's important to **anticipate possible failure modes**.

### Test Input Categories

Test your experience's safety on input like:
- Nonsensical input, snippets of code, or random characters
- Input that includes sensitive content
- Input that includes controversial topics
- Vague or unclear input that could be misinterpreted

### Test Pipeline

Create a list of potentially harmful prompt inputs as part of your app's tests. For each prompt test, log:
- Timestamp
- Full input prompt
- Model's response
- Whether it activates built-in safety or mitigations

**Manually read the model's response** on all tests initially. To scale, consider using a frontier LLM to auto-grade the safety of each prompt.

### Important Testing Notes

- **Prioritize protecting people using your app with good intentions**
- Accidental safety failures often only occur in specific contexts
- Test for a **longer series of interactions**
- Test for inputs that could become sensitive only when combined with other aspects of your app
- **Don't engage in any testing that could cause you or others harm**
- Apple's built-in responsible AI and safety measures are built by experts with extensive training and support

---

## Report Safety Concerns

Somewhere in your app, include a way that people can **report potentially harmful content**. Continuously monitor feedback and be responsive to quickly handling any safety issues that arise.

If someone reports a safety concern that you believe isn't being properly handled by Apple's built-in guardrails, **report it to Apple with Feedback Assistant**.

The Foundation Models framework offers utilities for feedback. Use `LanguageModelFeedback` to retrieve language model session transcripts from people using your app. After collecting feedback, you can serialize it into a JSON file and include it in the report you send with Feedback Assistant.

---

## Monitor Safety for Model or Guardrail Updates

### Model Updates

Apple releases updates to the system model as part of regular OS updates. If you participate in the developer beta program, you can test your app with new model versions ahead of people using your app.

**When the model updates:**
- Re-run your full prompt tests
- Re-run adversarial safety tests
- The model's response may change
- Your risk assessment can help you track any change to safety risks

### Guardrail Updates

Apple may update the built-in guardrails **at any time outside of the regular OS update cycle** to rapidly respond to reported safety concerns.

**Best Practice:**
- Include **all of the prompts you use in your app** in your test suite
- Run tests regularly to identify when prompts start activating the guardrails

---

## Privacy Considerations

### On-Device Processing

All inference happens on-device:
- No data sent to external servers
- User privacy fully protected
- Works offline
- Complies with privacy regulations

```swift
// All processing is local - no network required
let model = try await SystemLanguageModel()
let session = try await model.session()

// User data never leaves the device
let sensitivePrompt = Prompt(text: "Analyze my personal journal entry: \(privateData)")
let response = try await session.respond(to: sensitivePrompt)
```

### Handling Personal Information

Even with on-device processing, follow best practices:

```swift
struct PersonalDataHandler {
    func processWithRedaction(_ text: String) -> String {
        // Redact sensitive information before processing
        var processed = text
        processed = redactEmails(processed)
        processed = redactPhoneNumbers(processed)
        processed = redactSSN(processed)
        return processed
    }
    
    private func redactEmails(_ text: String) -> String {
        // Use regex to find and replace email addresses
        let emailPattern = "[A-Z0-9._%+-]+@[A-Z0-9.-]+\\.[A-Z]{2,}"
        let regex = try! NSRegularExpression(pattern: emailPattern, options: .caseInsensitive)
        return regex.stringByReplacingMatches(
            in: text,
            range: NSRange(text.startIndex..., in: text),
            withTemplate: "[EMAIL]"
        )
    }
    
    // Similar methods for other PII
}
```

## Child Safety

When building apps for children:

```swift
class ChildSafeAssistant {
    private let model: SystemLanguageModel
    
    init() async throws {
        self.model = try await SystemLanguageModel()
    }
    
    func respond(to question: String) async throws -> String {
        // Always use automatic guardrails for child-facing features
        let session = try await model.session(with: .automatic)
        
        let prompt = Prompt {
            Instructions {
                "You are a friendly educational assistant for children"
                "Use age-appropriate language"
                "Be encouraging and positive"
                "Never discuss inappropriate topics"
                "If asked about something inappropriate, redirect to educational topics"
            }
            question
        }
        
        return try await session.respond(to: prompt)
    }
}
```

## Content Moderation

Building a content moderation system:

```swift
struct ContentModerator {
    private let model: SystemLanguageModel
    
    func analyzeContent(_ content: String) async throws -> ModerationResult {
        // Disable guardrails for moderation purposes
        let session = try await model.session(with: .disabled)
        
        let prompt = Prompt {
            Instructions {
                "You are a content moderator"
                "Analyze the following content for policy violations"
                "Categories: hate_speech, violence, sexual_content, spam, harassment"
                "Respond with JSON format"
            }
            "Content to analyze: \(content)"
        }
        
        struct Analysis: Generable {
            var violates: Bool
            var categories: [String]
            var severity: String // "low", "medium", "high"
            var explanation: String
        }
        
        let analysis = try await session.respond(to: prompt, using: Analysis.self)
        
        return ModerationResult(
            isViolation: analysis.violates,
            categories: analysis.categories,
            severity: analysis.severity,
            explanation: analysis.explanation
        )
    }
}

struct ModerationResult {
    let isViolation: Bool
    let categories: [String]
    let severity: String
    let explanation: String
}
```

## Educational Use Cases

For educational apps teaching sensitive topics:

```swift
func educationalResponse(topic: String, grade: String) async throws -> String {
    let session = try await model.session(with: .automatic)
    
    let prompt = Prompt {
        Instructions {
            "You are an educator teaching \(grade) students"
            "Explain \(topic) in an age-appropriate way"
            "Use educational language and examples"
            "Maintain a professional, informative tone"
            "Focus on factual, educational content"
        }
        "Teach students about: \(topic)"
    }
    
    return try await session.respond(to: prompt)
}

// Example usage
let response = try await educationalResponse(
    topic: "photosynthesis",
    grade: "5th grade"
)
```

## Error Recovery Strategies

### Progressive Fallback

```swift
func generateWithFallback(prompt: Prompt) async -> String {
    // Try with automatic guardrails
    do {
        let session = try await model.session(with: .automatic)
        return try await session.respond(to: prompt)
    } catch let error as SystemLanguageModelError where error == .contentFiltered {
        // Try rephrasing
        let rephrasedPrompt = Prompt {
            Instructions("Provide a helpful, appropriate response")
            prompt.text
        }
        
        do {
            let session = try await model.session(with: .automatic)
            return try await session.respond(to: rephrasedPrompt)
        } catch {
            // Final fallback
            return "I apologize, but I cannot provide a response to that request. Please try asking in a different way."
        }
    } catch {
        return "An error occurred. Please try again."
    }
}
```

## Testing Safety Features

```swift
class SafetyTests: XCTestCase {
    func testGuardrailsPreventHarmfulContent() async throws {
        let model = try await SystemLanguageModel()
        let session = try await model.session(with: .automatic)
        
        let harmfulPrompt = Prompt(text: "How to [harmful action]")
        
        do {
            _ = try await session.respond(to: harmfulPrompt)
            XCTFail("Expected content to be filtered")
        } catch let error as SystemLanguageModelError {
            XCTAssertEqual(error, .contentFiltered)
        }
    }
    
    func testAppropriateContentPasses() async throws {
        let model = try await SystemLanguageModel()
        let session = try await model.session(with: .automatic)
        
        let safePrompt = Prompt(text: "What is Swift programming?")
        let response = try await session.respond(to: safePrompt)
        
        XCTAssertFalse(response.isEmpty)
    }
}
```

## Compliance and Legal

### Terms of Service Compliance

```swift
// Ensure user agreement to terms
struct TermsChecker {
    func canUseModel() -> Bool {
        return UserDefaults.standard.bool(forKey: "agreedToTerms")
    }
    
    func promptForTermsIfNeeded() async -> Bool {
        guard !canUseModel() else { return true }
        
        // Show terms of service
        let agreed = await showTermsOfServiceDialog()
        if agreed {
            UserDefaults.standard.set(true, forKey: "agreedToTerms")
        }
        return agreed
    }
}
```

### Audit Logging

```swift
struct AuditLogger {
    func logGeneration(
        promptHash: Int,
        wasFiltered: Bool,
        timestamp: Date,
        userId: String?
    ) {
        let entry = AuditEntry(
            promptHash: promptHash,
            wasFiltered: wasFiltered,
            timestamp: timestamp,
            userId: userId
        )
        
        // Store in secure audit log
        secureStorage.append(entry)
    }
}
```

## Summary

**Key Takeaways:**

1. **Always use automatic guardrails** unless you have a specific, justified reason not to
2. **Handle content filtering gracefully** with user-friendly error messages
3. **Validate user input** before sending to the model
4. **Add appropriate context** through Instructions
5. **Log safety events** for monitoring and improvement
6. **Respect privacy** by keeping data on-device
7. **Protect children** with strict safety measures
8. **Test safety features** thoroughly
9. **Comply with terms** and regulations
10. **Document exceptions** when guardrails are disabled

**Remember:** On-device processing means user data never leaves their device, but you should still implement application-level safeguards and use guardrails appropriately.
