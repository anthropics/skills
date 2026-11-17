# Guided Generation

## Overview

Guided generation allows you to constrain the language model's output to conform to specific Swift types. Instead of receiving unstructured text, you get type-safe Swift objects that match your data model.

### Why Use Guided Generation?

**Problem with Raw Strings:**
When you perform a request, the model returns a raw string in its natural language format. Raw strings require you to manually parse the details you want, which is:
- Error-prone
- Requires regex or string parsing
- No type safety
- Fragile to format changes

**Solution: Guided Generation**
The framework provides guided generation, which gives **strong guarantees** that the response is in a format you expect. The framework uses **constrained sampling** when generating output, which defines the rules on what the model can generate.

**Constrained sampling prevents the model from generating anything invalid.** For example, if you define a Float property, the model can only generate valid floating-point numbers—it cannot generate letters or invalid characters.

### Simple Example: Primitive Types

```swift
// Without guided generation - need to parse
let prompt = "How many tablespoons are in a cup?"
let session = LanguageModelSession(model: .default)
let response = try await session.respond(to: prompt)
// response = "There are 16 tablespoons in a cup."
// Now you need to extract "16"...

// With guided generation - type-safe!
let value = try await session.respond(to: prompt, generating: Float.self)
// value = 16.0 (guaranteed Float)
```

## Generable Protocol

The `Generable` protocol marks types that the language model can generate.

```swift
protocol Generable: Decodable {
    // No required methods - conformance indicates the type can be generated
}
```

Any `Decodable` type can conform to `Generable`:

```swift
struct Recipe: Generable {
    var title: String
    var ingredients: [String]
    var steps: [String]
}
```

## Basic Usage

### Simple Struct Generation

```swift
struct BookSummary: Generable {
    var title: String
    var author: String
    var mainThemes: [String]
    var rating: Int
}

let session = try await model.session()
let prompt = Prompt(text: "Summarize '1984' by George Orwell")

let summary = try await session.respond(to: prompt, using: BookSummary.self)
print(summary.title) // "1984"
print(summary.author) // "George Orwell"
print(summary.mainThemes) // ["totalitarianism", "surveillance", "freedom"]
```

### Nested Structures

```swift
struct Address: Generable {
    var street: String
    var city: String
    var state: String
    var zipCode: String
}

struct Person: Generable {
    var name: String
    var age: Int
    var address: Address
    var hobbies: [String]
}

let prompt = Prompt(text: "Create a profile for a fictional software engineer in San Francisco")
let person = try await session.respond(to: prompt, using: Person.self)
print(person.address.city) // "San Francisco"
```

## Generation Schema

For more control, use `GenerationSchema`:

```swift
struct GenerationSchema<T: Generable> {
    let type: T.Type
    
    init(_ type: T.Type) {
        self.type = type
    }
}
```

### Basic Schema Usage

```swift
struct MovieReview: Generable {
    var movieTitle: String
    var rating: Int // 1-5
    var pros: [String]
    var cons: [String]
    var recommendation: String
}

let schema = GenerationSchema(MovieReview.self)
let prompt = Prompt {
    Instructions("Provide honest movie reviews")
    "Review 'The Matrix'"
}

let review = try await session.respond(to: prompt, using: MovieReview.self)
```

## Dynamic Generation Schema

For runtime-defined schemas, use `DynamicGenerationSchema` to construct schemas programmatically at runtime:

### Creating Dynamic Schemas

```swift
// Array schema
let arraySchema = DynamicGenerationSchema(
    arrayOf: elementSchema,
    minimumElements: 1,
    maximumElements: 10
)

// Object schema with properties
let objectSchema = DynamicGenerationSchema(
    name: "Person",
    description: "A person object",
    properties: [
        "name": stringSchema,
        "age": integerSchema,
        "skills": skillsArraySchema
    ]
)

// Any-of schema (enum-like)
let statusSchema = DynamicGenerationSchema(
    name: "Status",
    description: "Task status",
    anyOf: [
        .constant("pending"),
        .constant("in_progress"),
        .constant("completed")
    ]
)

// Reference schema
let referenceSchema = DynamicGenerationSchema(
    referenceTo: "ExistingType"
)

// Schema from Generable type with guides
let guidedSchema = DynamicGenerationSchema(
    type: MyType.self,
    guides: [.minimum(0), .maximum(100)]
)
```

### Complete Dynamic Schema Example

```swift
// Define schemas at runtime based on user configuration
func createDynamicSchema(fieldTypes: [String: String]) -> DynamicGenerationSchema {
    var properties: [String: DynamicGenerationSchema] = [:]
    
    for (fieldName, fieldType) in fieldTypes {
        switch fieldType {
        case "string":
            properties[fieldName] = DynamicGenerationSchema(
                type: String.self,
                guides: []
            )
        case "integer":
            properties[fieldName] = DynamicGenerationSchema(
                type: Int.self,
                guides: [.minimum(0)]
            )
        case "array":
            properties[fieldName] = DynamicGenerationSchema(
                arrayOf: DynamicGenerationSchema(type: String.self, guides: []),
                minimumElements: 1,
                maximumElements: 10
            )
        default:
            break
        }
    }
    
    return DynamicGenerationSchema(
        name: "DynamicObject",
        description: "Runtime-defined object",
        properties: properties
    )
}

// Usage
let schema = createDynamicSchema(fieldTypes: [
    "name": "string",
    "age": "integer",
    "tags": "array"
])
```

## Guide Macro

The `@Guide` macro provides fine-grained control over generation for individual properties:

```swift
struct WeatherForecast: Generable {
    @Guide("City name, e.g., 'San Francisco'")
    var location: String
    
    @Guide("Temperature in Fahrenheit, between -50 and 150")
    var temperature: Int
    
    @Guide("One of: sunny, cloudy, rainy, snowy")
    var condition: String
    
    @Guide("Array of hourly forecasts for the next 24 hours")
    var hourlyForecast: [HourlyForecast]
}

struct HourlyForecast: Generable {
    @Guide("Hour in 24-hour format (0-23)")
    var hour: Int
    
    @Guide("Temperature in Fahrenheit")
    var temp: Int
}
```

### Using @Guide for Constraints

```swift
struct Product: Generable {
    @Guide("Product name, 2-50 characters")
    var name: String
    
    @Guide("Price in USD, positive decimal number")
    var price: Double
    
    @Guide("Exactly 5 tags, each 1 word")
    var tags: [String]
    
    @Guide("Description, 50-200 characters")
    var description: String
    
    @Guide("true if in stock, false otherwise")
    var inStock: Bool
}

let prompt = Prompt(text: "Create a product listing for wireless headphones")
let product = try await session.respond(to: prompt, using: Product.self)
```

## GenerationGuide API

The `GenerationGuide` struct provides programmatic control over how values are generated, offering more precise constraints than simple @Guide descriptions.

### Pattern Matching

```swift
struct FormData: Generable {
    @Guide("Email address", guides: .pattern("[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\\.[A-Z]{2,}"))
    var email: String
    
    @Guide("Phone number", guides: .pattern("\\d{3}-\\d{3}-\\d{4}"))
    var phoneNumber: String
    
    @Guide("Zip code", guides: .pattern("\\d{5}"))
    var zipCode: String
}
```

### Constant and AnyOf

```swift
struct Configuration: Generable {
    @Guide("Environment", guides: .anyOf(["development", "staging", "production"]))
    var environment: String
    
    @Guide("API version", guides: .constant("v2"))
    var apiVersion: String
}
```

### Array Constraints

```swift
struct Survey: Generable {
    @Guide("Exactly 5 questions", guides: .count(5))
    var questions: [String]
    
    @Guide("At least 3 tags", guides: .minimumCount(3))
    var tags: [String]
    
    @Guide("At most 10 categories", guides: .maximumCount(10))
    var categories: [String]
    
    @Guide("2-8 ratings", guides: [.minimumCount(2), .maximumCount(8)])
    var ratings: [Int]
}
```

### Element Constraints

```swift
struct NumberList: Generable {
    @Guide("Numbers between 1-100", guides: .element(.range(1...100)))
    var numbers: [Int]
    
    @Guide("Lowercase words", guides: .element(.pattern("[a-z]+")))
    var words: [String]
}
```

### Range Constraints

```swift
struct Measurement: Generable {
    @Guide("Temperature -50 to 150", guides: .range(-50...150))
    var temperature: Int
    
    @Guide("Percentage", guides: .range(0.0...100.0))
    var percentage: Double
}
```

### Min/Max Constraints

```swift
struct Limits: Generable {
    @Guide("Positive number", guides: .minimum(0))
    var value: Int
    
    @Guide("Score up to 100", guides: .maximum(100))
    var score: Int
    
    @Guide("Price between 10-1000", guides: [.minimum(10), .maximum(1000)])
    var price: Double
}
```

### Combining Multiple Guides

```swift
struct ValidatedInput: Generable {
    @Guide(
        "Username",
        guides: [
            .pattern("[a-zA-Z0-9_]+"),
            .minimumCount(3),
            .maximumCount(20)
        ]
    )
    var username: String
    
    @Guide(
        "Age",
        guides: [
            .minimum(13),
            .maximum(120)
        ]
    )
    var age: Int
    
    @Guide(
        "Skills",
        guides: [
            .minimumCount(1),
            .maximumCount(10),
            .element(.pattern("[A-Za-z]+"))
        ]
    )
    var skills: [String]
}
```

## Advanced Examples

### Event Planning

```swift
struct Event: Generable {
    @Guide("Event title")
    var title: String
    
    @Guide("ISO 8601 date string")
    var date: String
    
    @Guide("Duration in minutes")
    var duration: Int
    
    @Guide("List of required attendees")
    var attendees: [String]
    
    @Guide("Structured agenda items")
    var agenda: [AgendaItem]
}

struct AgendaItem: Generable {
    @Guide("Topic title")
    var topic: String
    
    @Guide("Duration in minutes")
    var duration: Int
    
    @Guide("Presenter name")
    var presenter: String
}

let prompt = Prompt {
    Instructions("You are an event planning assistant")
    "Plan a team retrospective meeting for next Friday with Alice, Bob, and Carol"
}

let event = try await session.respond(to: prompt, using: Event.self)
```

### Code Analysis

```swift
struct CodeReview: Generable {
    @Guide("List of issues found")
    var issues: [Issue]
    
    @Guide("List of suggestions")
    var suggestions: [String]
    
    @Guide("Overall quality score 1-10")
    var qualityScore: Int
    
    @Guide("Summary of review findings")
    var summary: String
}

struct Issue: Generable {
    @Guide("Issue severity: low, medium, high, critical")
    var severity: String
    
    @Guide("Line number where issue occurs")
    var lineNumber: Int
    
    @Guide("Description of the issue")
    var description: String
    
    @Guide("Suggested fix")
    var suggestedFix: String
}

let code = """
func processData(data: [String]) {
    for item in data {
        print(item)
    }
}
"""

let prompt = Prompt {
    Instructions("You are a code reviewer focused on Swift best practices")
    "Review this code: \(code)"
}

let review = try await session.respond(to: prompt, using: CodeReview.self)
```

### Recipe Generator

```swift
struct Recipe: Generable {
    @Guide("Recipe title")
    var title: String
    
    @Guide("Brief description, 1-2 sentences")
    var description: String
    
    @Guide("Preparation time in minutes")
    var prepTime: Int
    
    @Guide("Cooking time in minutes")
    var cookTime: Int
    
    @Guide("Number of servings")
    var servings: Int
    
    @Guide("List of ingredients with quantities")
    var ingredients: [Ingredient]
    
    @Guide("Ordered cooking steps")
    var steps: [String]
    
    @Guide("Difficulty: easy, medium, hard")
    var difficulty: String
}

struct Ingredient: Generable {
    @Guide("Ingredient name")
    var name: String
    
    @Guide("Amount needed")
    var amount: String
    
    @Guide("Unit of measurement")
    var unit: String
}

let prompt = Prompt(text: "Create a simple pasta carbonara recipe")
let recipe = try await session.respond(to: prompt, using: Recipe.self)

print("\(recipe.title) - \(recipe.difficulty)")
print("Time: \(recipe.prepTime + recipe.cookTime) minutes")
for ingredient in recipe.ingredients {
    print("- \(ingredient.amount) \(ingredient.unit) \(ingredient.name)")
}
```

## Enums and Constrained Values

```swift
enum Priority: String, Codable {
    case low, medium, high, urgent
}

enum Status: String, Codable {
    case todo, inProgress, completed, blocked
}

struct Task: Generable {
    @Guide("Task title")
    var title: String
    
    @Guide("Detailed description")
    var description: String
    
    @Guide("One of: low, medium, high, urgent")
    var priority: Priority
    
    @Guide("One of: todo, inProgress, completed, blocked")
    var status: Status
    
    @Guide("Estimated hours to complete")
    var estimatedHours: Double
    
    @Guide("List of assigned people")
    var assignees: [String]
}

let prompt = Prompt(text: "Create a high-priority task for implementing user authentication")
let task = try await session.respond(to: prompt, using: Task.self)
```

## Optional Properties

```swift
struct Article: Generable {
    @Guide("Article title")
    var title: String
    
    @Guide("Author name")
    var author: String
    
    @Guide("Publication date in YYYY-MM-DD format, if available")
    var publicationDate: String?
    
    @Guide("Article content")
    var content: String
    
    @Guide("List of tags, if any")
    var tags: [String]?
    
    @Guide("Featured image URL, if available")
    var imageURL: String?
}
```

## Best Practices

### 1. Use Descriptive Property Names

```swift
// Good
struct User: Generable {
    var firstName: String
    var lastName: String
    var emailAddress: String
}

// Less clear
struct User: Generable {
    var fn: String
    var ln: String
    var email: String
}
```

### 2. Provide Clear Guides

```swift
struct Appointment: Generable {
    @Guide("Appointment date in ISO 8601 format (YYYY-MM-DDTHH:mm:ss)")
    var dateTime: String
    
    @Guide("Duration in minutes, between 15 and 240")
    var duration: Int
}
```

### 3. Use Nested Types for Complex Data

```swift
struct Project: Generable {
    var name: String
    var milestones: [Milestone]
    var team: Team
}

struct Milestone: Generable {
    var title: String
    var deadline: String
    var deliverables: [String]
}

struct Team: Generable {
    var lead: String
    var members: [String]
}
```

### 4. Validate Generated Data

```swift
let session = try await model.session()
let prompt = Prompt(text: "Create a user profile")

let user = try await session.respond(to: prompt, using: User.self)

// Validate the generated data
guard !user.emailAddress.isEmpty,
      user.emailAddress.contains("@") else {
    throw ValidationError.invalidEmail
}
```

### 5. Combine with Instructions

```swift
let prompt = Prompt {
    Instructions {
        "Generate realistic test data"
        "Use proper formatting for dates and emails"
        "Ensure all required fields are populated"
    }
    "Create 3 sample user profiles for a social media app"
}

struct UserProfiles: Generable {
    var users: [User]
}

let profiles = try await session.respond(to: prompt, using: UserProfiles.self)
```

## Error Handling

```swift
do {
    let data = try await session.respond(to: prompt, using: MyStruct.self)
    // Process generated data
} catch {
    // Handle generation failures
    // May occur if the model cannot conform to the schema
    print("Failed to generate structured data: \(error)")
}
```

## Limitations

1. **Complexity**: Very complex nested structures may be challenging for the model
2. **Validation**: Generated data should be validated as the model may not perfectly follow constraints
3. **Token Limits**: Large schemas count toward session token limits
4. **Ambiguity**: Clear property names and guides lead to better results
