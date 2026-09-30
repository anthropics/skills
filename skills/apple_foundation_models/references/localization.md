# Localization

## Overview

The on-device system language model is **multilingual**, which means the **same model understands and generates text in any language that Apple Intelligence supports**. The model supports using different languages for:
- Prompts
- Instructions
- The output that the model produces

When you enhance your app with multilingual support, generate content in the language people prefer by:
1. Prompting the model with the language you prefer
2. Including the target language for your app in the instructions you provide the model
3. Determining the language or languages a person wants to use when they interact with your app
4. Gracefully handling languages that Apple Intelligence doesn't support

For more information about the languages and locales that Apple Intelligence supports, see the "Supported languages" section in **How to get Apple Intelligence**.

## Prompt the Model in the Language You Prefer

Write your app's **built-in prompts in the language with which you normally write code**, if Apple Intelligence supports that language. Translate your prompts into a supported language if your preferred language isn't supported.

**Important:** In the code below, **all inputs need to be in supported language** for the model to understand, including all `Generable` types and descriptions:

```swift
@Generable(description: "Basic profile information about a cat")
struct CatProfile {
    var name: String

    @Guide(description: "The age of the cat", .range(0...20))
    var age: Int

    @Guide(description: "One sentence about this cat's personality")
    var profile: String
}

#Playground {
    let response = try await LanguageModelSession().respond(
        to: "Generate a rescue cat",
        generating: CatProfile.self
    )
}
```

**Because the framework treats Generable types as model inputs**, the names of properties like `age` or `profile` are **just as important** as the `@Guide` descriptions for helping the model understand your request.

## Check a Person's Language Settings for Your App

People can use the Settings app on their device to configure the language they prefer to use **on a per-app basis**, which might differ from their default language.

If your app supports a language that Apple Intelligence doesn't, you need to **verify that the current language setting of your app is supported** before you call the model.

**Keep in mind:** Language support improves over time in newer model and OS versions. Thus, someone using your app with an older OS may not have the latest language support.

### Using supportsLocale(_:)

Before you call the model, run `supportsLocale(_:)` to verify the support for a locale. By default, the method uses `current`, which takes into account a person's current language and app-specific settings.

This method returns `true` if the model supports this locale, or if this locale is considered **similar enough** to a supported locale (e.g., en-AU and en-NZ):

```swift
if SystemLanguageModel.default.supportsLocale() {
    // Language is supported.
}
```

For advanced use cases where you need full language support details, use `supportedLanguages` to retrieve a list of languages supported by the on-device model.

## Handle Unsupported Language or Locale Errors

When you call `respond(to:options:)` on a `LanguageModelSession`, the Foundation Models framework checks:
- The language or languages of the input prompt text
- Whether your prompt asks the model to respond in any specific language or languages

If the model detects a language it doesn't support, the session throws `LanguageModelSession.GenerationError.unsupportedLanguageOrLocale(_:)`. Handle the error by **communicating to the person using your app that a language in their request is unsupported**.

If your app supports languages or locales that Apple Intelligence doesn't, help people that use your app by:
- Explaining that their language isn't supported by Apple Intelligence in your app
- Disabling your Foundation Models framework feature
- Providing an alternative app experience, if possible

**IMPORTANT:** Guardrails for model input and output safety are only for **supported languages and locales**. If a prompt contains sensitive content in an unsupported language (typically a short phrase mixed-in with text in a supported language), it might not throw an `unsupportedLanguageOrLocale` error. If unsupported-language detection fails, the guardrails may also fail to flag that short, unsupported content.

---

## Use Instructions to Set the Locale and Language

For locales other than United States English, you can **improve response quality** by telling the model which locale to use by detailing a set of `Instructions`.

Start with the **exact phrase in English**. This special phrase comes from the model's training and reduces the possibility of hallucinations in multilingual situations:

```swift
func localeInstructions(for locale: Locale = Locale.current) -> String {
    if Locale.Language(identifier: "en_US").isEquivalent(to: locale.language) {
        // Skip the locale phrase for U.S. English.
        return "" 
    } else {
        // Specify the person's locale with the exact phrase format.
        return "The person's locale is \(locale.identifier)."
    }
}
```

### Explicitly Set the Model Output Language

After you set the locale in `Instructions`, you may need to **explicitly set the model output language**.

**By default**, the model responds in the language or languages of its inputs. If your app supports multiple languages, prompts that you write and inputs from people using your app might be in different languages. For example, if you write your built-in prompts in Spanish, but someone using your app writes inputs in Dutch, the model may respond in either or both languages.

Use `Instructions` to explicity tell the model which language or languages with which it needs to respond. You can phrase this request in different ways, for example:
- "You MUST respond in Italian"
- "You MUST respond in Italian and be mindful of Italian spelling, vocabulary, entities, and other cultural contexts of Italy."

These instructions can be in the language you prefer.

```swift
let session = LanguageModelSession(
    instructions: "You MUST respond in U.S. English."
)
let prompt = // A prompt that contains Spanish and Italian.
let response = try await session.respond(to: prompt)
```

**Finally**, thoroughly test your instructions to ensure the model is responding in the way you expect. If the model isn't following your instructions, try capitalized words like "MUST" or "ALWAYS" to strengthen your instructions.

## Example: Multilingual Conversations

```swift
// Session maintains language consistency
let session = LanguageModelSession(
    instructions: Instructions("You are a multilingual assistant. You MUST respond in the same language as the prompt.")
)

// First message in English
let response1 = try await session.respond(
    to: Prompt("Hello, can you help me?")
)

// Switch to Spanish
let response2 = try await session.respond(
    to: Prompt("Ahora responde en español")
)
// Model switches to Spanish

// Back to English
let response3 = try await session.respond(
    to: Prompt("Switch back to English please")
)
// Model switches back to English
```

## Best Practices

### 1. Check Locale Support

```swift
func createLocalizedSession() async throws -> LanguageModelSession {
    let model = SystemLanguageModel(useCase: .general)
    
    // Check if user's locale is supported
    guard model.supportsLocale(Locale.current) else {
        // Fall back to English or show warning
        print("Warning: User's locale not fully supported")
        // You can still use the model, it will do its best
    }
    
    let session = LanguageModelSession(model: model)
    return session
}
```

### 2. Provide Language Context

```swift
let userLanguage = Locale.current.languageCode ?? "en"

let prompt = Prompt {
    Instructions {
        "Respond in \(Locale.current.localizedString(forLanguageCode: userLanguage) ?? "English")"
        "Use culturally appropriate examples"
    }
    userQuestion
}
```

### 3. Handle Mixed Languages

```swift
let prompt = Prompt {
    Instructions {
        "You can understand questions in any language"
        "Always respond in the same language as the question"
        "If the question mixes languages, respond in the primary language"
    }
    "What is SwiftUI? ¿Qué es?"
}
```

### 4. Regional Variations

```swift
// Handle regional language differences
let region = Locale.current.regionCode ?? "US"

let prompt = Prompt {
    Instructions {
        "Use \(region) regional conventions"
        "Use local date formats, measurements, and terminology"
    }
    "When is Thanksgiving?"
}
// US: November, Canada: October
```

## Localization Patterns

### Date and Time Formatting

```swift
let prompt = Prompt {
    Instructions {
        "Use the user's locale for date formatting"
        "Region: \(Locale.current.identifier)"
    }
    "What's the date format for today?"
}

// US locale: MM/DD/YYYY
// European locale: DD/MM/YYYY
```

### Number Formatting

```swift
let prompt = Prompt {
    Instructions("Format numbers according to \(Locale.current.identifier) conventions")
    "What is 1234567.89 formatted for display?"
}

// US: 1,234,567.89
// Europe: 1.234.567,89
```

### Currency

```swift
let currencyCode = Locale.current.currencyCode ?? "USD"

let prompt = Prompt {
    Instructions("Use \(currencyCode) when discussing money")
    "How much does a coffee cost?"
}
```

## Example: Multilingual App

```swift
class MultilingualAssistant {
    private let model: SystemLanguageModel
    private var session: LanguageModelSession?
    
    init() async throws {
        self.model = SystemLanguageModel(useCase: .general)
        
        // Check locale support
        if !model.supportsLocale(Locale.current) {
            print("Warning: Limited support for current locale")
        }
        
        // Create session with language context
        let languageName = Locale.current.localizedString(
            forLanguageCode: Locale.current.languageCode ?? "en"
        ) ?? "English"
        
        self.session = LanguageModelSession(
            model: model,
            instructions: Instructions {
                "You are a helpful assistant"
                "Respond in \(languageName)"
                "Use appropriate cultural references"
                "Format dates, numbers, and currency according to \(Locale.current.identifier)"
            }
        )
    }
    
    func ask(_ question: String) async throws -> String {
        guard let session = session else {
            throw AssistantError.notInitialized
        }
        
        return try await session.respond(to: Prompt(question))
    }
    
    func switchLanguage(_ locale: Locale) async throws {
        guard model.supportsLocale(locale) else {
            throw AssistantError.localeNotSupported
        }
        
        let languageName = locale.localizedString(
            forLanguageCode: locale.languageCode ?? "en"
        ) ?? "English"
        
        self.session = LanguageModelSession(
            model: model,
            instructions: Instructions {
                "Respond in \(languageName)"
                "Use \(locale.identifier) conventions"
            }
        )
    }
}

enum AssistantError: Error {
    case notInitialized
    case localeNotSupported
}
```

## Language Fallbacks

```swift
func getPreferredLanguages() -> [String] {
    // Get user's preferred languages in order
    return Locale.preferredLanguages.compactMap { identifier in
        let locale = Locale(identifier: identifier)
        return locale.languageCode
    }
}

func selectSupportedLanguage(from preferences: [String], model: SystemLanguageModel) -> String? {
    for langCode in preferences {
        let locale = Locale(identifier: langCode)
        if model.supportsLocale(locale) {
            return langCode
        }
    }
    return "en" // Fallback to English
}

// Usage
let model = SystemLanguageModel(useCase: .general)
let preferences = getPreferredLanguages()
let selectedLang = selectSupportedLanguage(from: preferences, model: model)

let prompt = Prompt {
    Instructions("Respond in language code: \(selectedLang ?? "en")")
    userQuestion
}
```

## Testing Localization

```swift
class LocalizationTests: XCTestCase {
    func testMultipleLanguages() async throws {
        let model = SystemLanguageModel(useCase: .general)
        
        let languages = [
            ("en", "What is SwiftUI?"),
            ("es", "¿Qué es SwiftUI?"),
            ("fr", "Qu'est-ce que SwiftUI?"),
            ("de", "Was ist SwiftUI?")
        ]
        
        for (langCode, question) in languages {
            let locale = Locale(identifier: langCode)
            
            if model.supportsLocale(locale) {
                let session = LanguageModelSession(model: model)
                let response = try await session.respond(to: Prompt(question))
                
                XCTAssertFalse(response.isEmpty, "Response should not be empty for \(langCode)")
                print("\(langCode): \(response.prefix(50))...")
            } else {
                print("Language \(langCode) not supported, skipping")
            }
        }
    }
}
```

## Common Pitfalls

### 1. Don't Assume English

```swift
// Bad - Assumes English
let prompt = Prompt("Explain...")

// Good - Respects user language
let prompt = Prompt {
    Instructions("Respond in the user's preferred language")
    userQuestion
}
```

### 2. Cultural Sensitivity

```swift
let prompt = Prompt {
    Instructions {
        "Be culturally sensitive"
        "Avoid idioms that don't translate"
        "Use appropriate examples for \(Locale.current.regionCode ?? "US")"
    }
    userQuestion
}
```

### 3. Mixed Content

```swift
// Handle code + natural language
let prompt = Prompt {
    Instructions {
        "Explain concepts in \(currentLanguage)"
        "Keep code examples and technical terms in English"
        "Comment code in \(currentLanguage)"
    }
    "Explain this Swift code: \(codeSnippet)"
}
```

## Summary

**Key Points:**

1. **Automatic Language Detection** - Model uses device language by default
2. **Check Support** - Use `supportsLocale(_:)` before assuming support
3. **Explicit Instructions** - Request specific languages in prompts
4. **Regional Awareness** - Handle date, number, and currency formats
5. **Fallback Strategy** - Provide fallback languages for unsupported locales
6. **Cultural Sensitivity** - Adapt content to regional norms
7. **Mixed Languages** - Handle code examples with multilingual explanations
8. **Test Thoroughly** - Verify behavior across different locales

Foundation Models provides robust multilingual support, allowing your app to serve users worldwide in their preferred language.
