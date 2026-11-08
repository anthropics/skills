# Prompting

## Overview

Prompting is the primary way to interact with Apple's Foundation Models. The framework provides a flexible `Prompt` API that supports both simple text prompts and complex multi-part prompts with system instructions.

### On-Device Model Differences

**Important:** Many prompting techniques are designed for server-based "frontier" foundation models with larger context windows and thinking capabilities. When prompting an on-device model, your prompt engineering technique is **even more critical** because the model is much smaller.

**Key Differences:**
- ✅ **On-Device**: Smaller, faster, private, offline-capable
- ⚠️ **Smaller Context**: Limited conversation history
- ⚠️ **Less "Thinking"**: Best with direct, specific prompts
- ✅ **Low Latency**: Immediate responses
- ✅ **Privacy**: No data leaves device

### Prompting Best Practices for On-Device Models

To generate accurate, hallucination-free responses, use these techniques:

1. **Use simple, clear instructions**
2. **Iterate and improve your prompt based on the output you receive in testing**
3. **Provide the model with a reasoning field before answering a prompt**
4. **Reduce the thinking the model needs to do**
5. **Split complex prompts into a series of simpler requests**
6. **Add "logic" to conditional prompts with "if-else" statements**
7. **Leverage shot-based prompting** — such as one-shot, few-shot, or zero-shot prompts — to provide the model with specific examples of what you need

You'll need to test your prompts throughout development and evaluate the output to provide a great user experience.

---

## Keep Prompts Simple and Clear

Effective prompts use **simple language** that tells the model what output you want it to provide. The model processes text in units, called **tokens**, and each model has a maximum number of tokens it can process — the **context window size**.

An on-device model has **fewer parameters and a small context window**, so it doesn't have the resources to handle long or confusing prompts. Input to a frontier model might be the length of a full document, but your input to the on-device model needs to be **short and succinct**.

Ask yourself whether your prompt is **understandable to a human if they read it quickly**, and consider additional strategies to adjust your tone and writing style:

| ✅ Prompting strategies to use | 🚫 Prompting strategies to avoid |
|-------------------------------|----------------------------------|
| Focus on a single, well-defined goal | Combining multiple unrelated requests |
| Be direct with imperative verbs like "List" or "Create" | Unnecessary politeness or hedging |
| Tell the model what role to play, for example, an interior designer | Passive voice, for example, "code needs to be optimized" |
| Write in direct, conversational tone with simple, clear sentences | Jargon the model might not understand or interpret incorrectly |
| State your request clearly | Too short of a prompt that doesn't outline the task |
| Limit your prompt to one to three paragraphs | Too long of a prompt that makes it hard to identify what the task is |

### ✅ Concise and Direct

```
Given a person's home-decor transactions and search history, generate three categories they might be interested in, starting with the most relevant category. Generate two more categories related to home-decor but that are not in their transaction or search history.
```

### 🚫 Long and Indirect

```
The person's input contains their recent home-decor transaction history along with their recent search history. The response should be a list of existing categories of content the person might be interested relevant to their search and transactions, ordered so that the first categories in the list are most relevant. For inspiration, the response should also include new categories that spark creative ideas that aren't covered in any of the categories you generate.
```

An on-device model may get confused with a long and indirect instruction because it contains unnecessary language that doesn't add value. Instead of indirectly implying what the model needs to do, **write a direct command** to improve the clarity of the prompt for better results. This clarity also reduces the complexity and context window size for the on-device model.

---

## Give the Model a Role, Persona, and Tone

By default, the on-device model typically responds to questions in a **neutral and respectful tone**, with a business-casual persona. Similar to frontier models, you can provide a **role or persona** to dramatically change how the on-device model responds to your prompt.

A **role** is the functional position or job that you instruct the model to assume, while a **persona** reflects the personality of the model. You often use both in prompts; for example:

```
You are a senior software engineer who values mentoring junior developers.
```

Here the **role** is "a senior software engineer," and the **persona** is "mentoring junior developers."

The model phrases its response differently to match a persona, for example, "mentoring junior developers" or "evaluating developer coding" even when you give it the same input for the same task.

### To Give the Model a Role

Use the phrase **"you are"**:

**English Teacher:**
```
You are an expert English teacher. Provide feedback on the person's sentence to help them improve clarity.
```

**Cowboy:**
```
You are a lively cowboy who loves to chat about horses and make jokes. Provide feedback on the person's sentence to help them improve clarity.
```

Use the phrase **"expert"** to get the model to speak with more authority and detail on a topic.

### Provide a Role for the Person

Similarly, change the model's behavior by providing a role or persona for the person using your app. By default, the on-device model thinks it's talking to a person, so **tell the model more about who that person is**:

**Student:**
```
The person is a first-grade English student. Give the person feedback on their writing.
```

**Ghost:**
```
Greet a customer who enters your alchemy shop. The customer is a friendly ghost.
```

The **student persona** causes the model to respond as if speaking to a child in the first grade, while the **ghost persona** causes the model to respond as if speaking to a ghost in an alchemy shop.

### Change the Model's Tone

Change the model's tone by **writing your prompt in a voice you want the model to match**. For example, if you write your prompt in a peppy and cheerful way, or talk like a cowboy, the model responds with a matching tone.

**Professional:**
```
Communicate as an experienced interior designer consulting with a client. Occasionally reference design elements like harmony, proportion, or focal points.
```

**Medieval Scholar:**
```
Communicate as a learned scribe from a medieval library. Use slightly archaic language ("thou shalt," "wherein," "henceforth") but keep it readable.
```

---

## Iterate and Improve Instruction Following

**Instruction following** refers to a foundation model's ability to carry out a request exactly as written in your `Prompt` and `Instructions`. Prompt engineering involves **iteration to test and refine input** — based on the results you get — to improve accuracy and consistency.

If you notice the model isn't following instructions as well as you need, consider the following strategies:

| Strategy | Approach |
|----------|----------|
| **Improve clarity** | Improve the wording of your input to make it more direct, concise, and easier to read. |
| **Use emphasis** | Emphasize the importance of a command by adding words like "must," "should," "do not," or "avoid." |
| **Repeat yourself** | Try repeating key instructions at the end of your input to emphasize the importance. |

Instead of trying to enforce accuracy, use a succinct prompt like "Answer this question" and evaluate the results you get.

After you try any strategy, **take the time to evaluate it** to see if the result gets closer to what you need. If the model can't follow your prompt, it might be unreliable in some use cases. Try cutting back the number of times you repeat a phrase, or the number of words you emphasize, to make your prompt more effective. **Unreliable prompts break easily when conditions change slightly.**

Another prompting strategy is to **split your request into a series of simpler requests**. This is particularly useful after trying different strategies that don't improve the quality of the results.

## Prompt Struct

The `Prompt` struct represents input to the language model.

### Simple Text Prompts

```swift
// Create a basic prompt
let prompt = Prompt(text: "What is SwiftUI?")

// Use with a session
let session = try await model.session()
let response = try await session.respond(to: prompt)
```

### Prompt Builder Syntax

For more complex prompts, use the result builder syntax:

```swift
let prompt = Prompt {
    Instructions("You are a helpful assistant")
    "Explain the concept of closures in Swift"
}
```

## Instructions

The `Instructions` struct provides system-level directives that guide the model's behavior.

### Basic Instructions

```swift
let prompt = Prompt {
    Instructions("You are an expert Swift developer")
    "How do I implement a custom collection type?"
}
```

### Multiple Instructions

You can combine multiple instruction components:

```swift
let prompt = Prompt {
    Instructions {
        "You are a technical writing assistant"
        "Always use clear, concise language"
        "Provide code examples when relevant"
    }
    "Explain property wrappers in SwiftUI"
}
```

### Conditional Instructions (Game/Dynamic Content)

For game or dynamic scenarios, use IF-THEN logic:

```swift
let instructions = """
    You are a friendly innkeeper. Generate a greeting to a new guest that walks in the door.
    IF the guest is a sorcerer, comment on their magical appearance.
    IF the guest is a bard, ask if they're willing to play music for the inn tonight.
    IF the guest is a soldier, ask if there's been any dangerous activity in the area.
    OTHERWISE, give them a warm, generic welcome.
    
    Keep your response to 2-3 sentences maximum.
    """

let prompt = Prompt {
    Instructions(instructions)
    "The guest is a \(guestRole). Greet them."
}
```

**Alternative: Dynamic Instructions (Recommended for On-Device)**

When the on-device model output doesn't meet your expectations, try **customizing your conditional prompt to the current context** using programming logic instead of embedding if-else logic into your prompt:

```swift
// ❌ TOO MUCH conditional complexity for on-device model
let instructions = """
    You are a friendly innkeeper. Generate a greeting to a new guest that walks in the door.
    IF the guest is a sorcerer, comment on their magical appearance.
    IF the guest is a bard, ask if they're willing to play music for the inn tonight.
    IF the guest is a soldier, ask if there's been any dangerous activity in the area.
    There is one single and one double room available.
    """

// ✅ BETTER: Use programming logic to customize the prompt
var customGreeting = ""
switch role {
case .bard:
    customGreeting = """
        This guest is a bard. Ask if they're willing to play music for the inn tonight.
        """
case .soldier:
    customGreeting = """
        This guest is a soldier. Ask if there's been any dangerous activity in the area.
        """
case .sorcerer:
    customGreeting = """
        This guest is a sorcerer. Comment on their magical appearance.
        """
default:
    customGreeting = "This guest is a weary traveler."
}

let instructions = """
    You are a friendly inn keeper. Generate a greeting to a new guest that walks in the door.
    \(customGreeting)
    There is one single and one double room available.
    """
```

When you customize instructions programmatically, the model **doesn't get distracted or confused by conditionals that don't apply** in the situation. This approach also **reduces the context window size**.

---

## Reduce How Much Thinking the Model Needs to Do

A model's **reasoning ability** is how well it thinks through a problem like a human, handles logical puzzles, or creates a logical plan to handle a request. Because of their smaller size, **on-device models have limited reasoning abilities**. You may be able to help an on-device model think through a challenging task by providing additional support for its reasoning.

### Step-by-Step Approach

For complex tasks, simple language prompts might not have enough detail about how the model can accomplish a task. Instead, **reduce the reasoning burden on the model by giving it a step-by-step plan**. This approach tells the model more precisely how to do the task:

```
Given a person's home-decor transactions and search history related to couches:

1. Choose four home furniture categories that are most relevant to this person.
2. Recommend two more categories related to home-decor.
3. Return a list of relevant and recommended categories, ordered by most relevant to least.
```

If you find the model isn't accomplishing the task reliably, **break up the steps across multiple `LanguageModelSession` instances** to focus on one part at a time with a new context window. Typically, it's a best practice to start with a single request because multiple requests can result in longer inference time. But, if the result doesn't meet your expectations, try splitting steps into multiple requests.

---

## Provide Simple Input-Output Examples (Few-Shot Prompting)

**Few-shot prompting** is when you provide the on-device model with a few examples of the output you want. For example, the following shows the model different kinds of coffee shop customers it needs to generate:

```swift
// Instructions that contain JSON key-value pairs that represent the structure
// of a customer. The structure tells the model that each customer must have
// a `name`, `imageDescription`, and `coffeeOrder` fields.
let instructions = """
    Create an NPC customer with a fun personality suitable for the dream realm. \
    Have the customer order coffee. Here are some examples to inspire you:

    {name: "Thimblefoot", imageDescription: "A horse with a rainbow mane", \
    coffeeOrder: "I would like a coffee that's refreshing and sweet, like the grass in a summer meadow."}
    {name: "Spiderkid", imageDescription: "A furry spider with a cool baseball cap", \
    coffeeOrder: "An iced coffee please, that's as spooky as I am!"}
    {name: "Wise Fairy", imageDescription: "A blue, glowing fairy that radiates wisdom and sparkles", \
    coffeeOrder: "Something simple and plant-based, please. A beverage that restores my wise energy."}
    """
```

Few-shot prompting also works with **guided generation**, which formats the model's output by using a custom type you define. In the previous prompt, each example might correspond to a `Generable` structure you create named `NPC`:

```swift
@Generable
struct NPC: Equatable {
    let name: String
    let coffeeOrder: String
    let imageDescription: String
}
```

**On-device models need simpler examples** for few-shot prompts than what you can use with server-based frontier models. Try giving the model **between 2-15 examples**, and keep each example as simple as possible. If you provide a long or complex example, the on-device model may start to repeat your example or hallucinate details of your example in its response.

---

## Handle On-Device Reasoning

Reasoning prompt techniques, like "think through this problem step by step", can result in **unexpected text being inserted into your `Generable` structure** if the model doesn't have a place for its reasoning.

To keep reasoning explanations out of your structure, try **giving the model a specific field where it can put its reasoning**. Make sure the reasoning field is the **first property** so the model can provide reasoning details before answering the prompt:

```swift
@Generable
struct ReasonableAnswer {
    // A property the model uses for reasoning.
    var reasoningSteps: String
    
    @Guide(description: "The answer only.")
    var answer: MyCustomGenerableType // Replace with your custom generable type.
}
```

Using your custom `Generable` type, prompt the model:

```swift
let instructions = """
    Answer the person's question.
    1. Begin your response with a plan to solve this question.
    2. Follow your plan's steps and show your work.
    3. Deliver the final answer in `answer`.
    """
var session = LanguageModelSession(instructions: instructions)

// The answer should be 30 days.
let prompt = "How many days are in the month of September?"
let response = try await session.respond(
    to: prompt,
    generating: ReasonableAnswer.self
)
```

You may see the model **fail to reason its way to a correct answer**, or it may answer **unreliably** — occasionally answering correctly, and sometimes not. If this happens, the tasks in your prompt may be **too difficult for the on-device model to process**, regardless of how you structure the prompt.

---

## Provide Actionable Feedback

When you encounter something with the on-device model that you expect to work but it doesn't, **file a report that includes your prompt with Feedback Assistant** to help improve the system model. To submit feedback about model behavior through Feedback Assistant, see `logFeedbackAttachment(sentiment:issues:desiredOutput:)`.

## Creating Effective Prompts

### Be Specific

```swift
// Less effective
let prompt = Prompt(text: "Tell me about arrays")

// More effective
let prompt = Prompt {
    Instructions("You are a Swift programming tutor")
    "Explain how Swift arrays differ from NSArray, including performance characteristics and type safety benefits"
}
```

### Provide Context

```swift
let prompt = Prompt {
    Instructions {
        "You are helping a beginner iOS developer"
        "Explain concepts simply with practical examples"
    }
    "I'm building my first app. How should I structure my SwiftUI views?"
}
```

### Use Examples (Few-Shot Prompting)

```swift
let prompt = Prompt {
    Instructions {
        "You are a code reviewer"
        "Format your responses as: Issue, Suggestion, Corrected Code"
    }
    """
    Review this Swift code:
    
    func fetchData() {
        let url = URL(string: userInput)!
        let data = try! Data(contentsOf: url)
    }
    """
}
```

## Response Methods

### respond(to:)

Generates a complete response before returning:

```swift
let prompt = Prompt {
    Instructions("You are a concise technical writer")
    "Explain Swift's ARC in 3 sentences"
}

let session = try await model.session()
let response = try await session.respond(to: prompt)
print(response)
// Waits for complete response, then prints all at once
```

**Best for:**
- Short responses
- When you need the complete text before processing
- Structured output generation

### streamResponse(to:)

Streams response tokens as they're generated:

```swift
let prompt = Prompt {
    Instructions("You are a creative writing assistant")
    "Write a short story about a curious robot"
}

let session = try await model.session()
for try await token in session.streamResponse(to: prompt) {
    print(token, terminator: "")
}
print() // Add newline at end
```

**Best for:**
- Long-form content
- Real-time UI updates
- Better perceived performance
- Cancellable generation

## Advanced Prompting Techniques

### Role-Based Prompting

```swift
let prompt = Prompt {
    Instructions {
        "You are an experienced iOS architect"
        "Focus on scalability and maintainability"
        "Consider performance implications"
    }
    "Should I use Core Data or SwiftData for a social media app?"
}
```

### Constrained Output Format

```swift
let prompt = Prompt {
    Instructions {
        "You are a technical reviewer"
        "Format responses as JSON with keys: summary, issues, recommendations"
    }
    "Review this networking code: \(codeSnippet)"
}
```

### Chain of Thought

```swift
let prompt = Prompt {
    Instructions("Think step-by-step before providing your answer")
    "How would I implement undo/redo functionality in a drawing app?"
}
```

### Temperature Control (Implicit)

While you cannot directly set temperature, you can influence output randomness through instructions:

```swift
// More deterministic
let prompt = Prompt {
    Instructions {
        "Provide the single most common solution"
        "Be precise and factual"
    }
    "How do I parse JSON in Swift?"
}

// More creative
let prompt = Prompt {
    Instructions {
        "Be creative and explore multiple approaches"
        "Consider unconventional solutions"
    }
    "How could I make my app's UI more engaging?"
}
```

## Conversation Context

Sessions maintain conversation history automatically:

```swift
let session = try await model.session()

// First turn
let response1 = try await session.respond(
    to: Prompt(text: "I'm building a weather app")
)

// Second turn - model remembers context
let response2 = try await session.respond(
    to: Prompt(text: "How should I handle location permissions?")
)
// Model knows you're asking about location permissions for a weather app
```

## Prompt Engineering Tips

### 1. Start with Instructions

```swift
let prompt = Prompt {
    Instructions("You are an expert in SwiftUI animations")
    "How do I create a spring animation?"
}
```

### 2. Be Direct

```swift
// Good
let prompt = Prompt(text: "List 3 ways to optimize image loading in iOS")

// Less effective
let prompt = Prompt(text: "Can you maybe tell me some ways I might be able to optimize images?")
```

### 3. Specify Output Format

```swift
let prompt = Prompt {
    Instructions {
        "Provide code examples in Swift"
        "Include inline comments"
        "Show import statements"
    }
    "How do I use async/await with URLSession?"
}
```

### 4. Use Delimiters for Code

```swift
let code = """
class ViewController: UIViewController {
    // ... code
}
"""

let prompt = Prompt {
    Instructions("You are a code reviewer")
    """
    Review the following Swift code:
    
    ```swift
    \(code)
    ```
    """
}
```

### 5. Handle Edge Cases

```swift
let prompt = Prompt {
    Instructions {
        "If the question is unclear, ask for clarification"
        "If you're unsure, say so"
        "Provide reasoning for your suggestions"
    }
    "How do I fix the bug?"
}
```

## Error Handling

```swift
do {
    let response = try await session.respond(to: prompt)
} catch {
    // Handle content filtering, token limits, etc.
    print("Failed to generate response: \(error)")
}
```

## Representable Protocols

### InstructionsRepresentable

The `InstructionsRepresentable` protocol allows custom types to be used as instructions.

```swift
protocol InstructionsRepresentable {
    var instructionsRepresentation: Instructions { get }
}
```

**Usage:**

```swift
struct SystemRole: InstructionsRepresentable {
    let role: String
    let context: String
    
    var instructionsRepresentation: Instructions {
        Instructions {
            "You are a \(role)"
            "Context: \(context)"
        }
    }
}

// Use custom instruction type
let role = SystemRole(role: "Swift expert", context: "helping iOS developers")
let session = LanguageModelSession(
    model: model,
    instructions: role.instructionsRepresentation
)
```

### PromptRepresentable

The `PromptRepresentable` protocol allows custom types to be used as prompts.

```swift
protocol PromptRepresentable {
    var promptRepresentation: Prompt { get }
}
```

**Usage:**

```swift
struct CodeReviewRequest: PromptRepresentable {
    let code: String
    let language: String
    let focusAreas: [String]
    
    var promptRepresentation: Prompt {
        Prompt {
            Instructions("You are a code reviewer")
            """
            Review this \(language) code:
            \(code)
            
            Focus on: \(focusAreas.joined(separator: ", "))
            """
        }
    }
}

// Use custom prompt type
let request = CodeReviewRequest(
    code: myCode,
    language: "Swift",
    focusAreas: ["performance", "safety", "style"]
)

let response = try await session.respond(to: request.promptRepresentation)
```

**Benefits:**
- Type-safe prompt construction
- Reusable prompt templates
- Encapsulated prompt logic
- Better code organization

## Best Practices

1. **Use Instructions for Behavior**: Set the model's role and output format with `Instructions`
2. **Keep Prompts Focused**: One clear question or task per prompt
3. **Provide Examples**: Show the model what you want with examples
4. **Iterate**: Refine prompts based on responses
5. **Use Streaming for Long Content**: Better user experience with `streamResponse(to:)`
6. **Maintain Context**: Reuse sessions for related queries
7. **Handle Errors Gracefully**: Always wrap generation in try-catch blocks
