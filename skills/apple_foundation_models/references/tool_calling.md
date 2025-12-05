# Tool Calling

## Overview

Tool calling enables the language model to interact with external systems and APIs. The model can decide when to call tools, extract the necessary arguments, and incorporate tool results into its responses.

## Tool Protocol

The `Tool` protocol defines the interface for creating custom tools:

```swift
protocol Tool {
    /// Description of what the tool does
    static var description: String { get }
    
    /// The arguments structure for this tool
    associatedtype Arguments: Decodable
    
    /// Execute the tool with the provided arguments
    func call(arguments: Arguments) async throws -> String
}
```

## Basic Tool Implementation

### Database Search Tool (From Apple Sample)

```swift
struct BreadDatabaseTool: Tool {
    let name = "searchBreadDatabase"
    let description = "Searches a local database for bread recipes."
    
    @Generable
    struct Arguments {
        @Guide(description: "The type of bread to search for")
        var searchTerm: String
        
        @Guide(description: "Maximum number of results to return", .range(1...10))
        var maxResults: Int?
    }
    
    func call(arguments: Arguments) async throws -> String {
        let limit = arguments.maxResults ?? 5
        
        // Query local database
        let recipes = database.searchRecipes(
            matching: arguments.searchTerm,
            limit: limit
        )
        
        // Format results for the model
        if recipes.isEmpty {
            return "No bread recipes found for '\(arguments.searchTerm)'"
        }
        
        let recipeList = recipes.map { recipe in
            "- \(recipe.name): \(recipe.description)"
        }.joined(separator: "\n")
        
        return "Found \(recipes.count) bread recipes:\n\(recipeList)"
    }
}

// Use the tool
let session = LanguageModelSession(
    model: model,
    tools: [BreadDatabaseTool()]
)

let response = try await session.respond(
    to: Prompt("Find three sourdough bread recipes")
)
// Model automatically calls BreadDatabaseTool and incorporates results
```

### Weather Tool Example

```swift
struct WeatherTool: Tool {
    static let description = "Gets current weather information for a specified location"
    
    struct Arguments: Decodable {
        let location: String
        let units: String? // "fahrenheit" or "celsius", defaults to fahrenheit
    }
    
    func call(arguments: Arguments) async throws -> String {
        let units = arguments.units ?? "fahrenheit"
        
        // In a real implementation, call a weather API
        let weather = try await fetchWeather(
            location: arguments.location,
            units: units
        )
        
        return """
        Current weather in \(arguments.location):
        Temperature: \(weather.temperature)°\(units == "celsius" ? "C" : "F")
        Conditions: \(weather.conditions)
        Humidity: \(weather.humidity)%
        """
    }
    
    private func fetchWeather(location: String, units: String) async throws -> Weather {
        // Implementation: Call actual weather API
        // For demo purposes:
        return Weather(
            temperature: 72,
            conditions: "Sunny",
            humidity: 45
        )
    }
}

struct Weather {
    let temperature: Int
    let conditions: String
    let humidity: Int
}
```

### Using the Weather Tool

```swift
let session = try await model.session()
let weatherTool = WeatherTool()

let prompt = Prompt {
    Instructions("You are a helpful assistant with access to weather information")
    "What's the weather like in San Francisco?"
}

let response = try await session.respond(
    to: prompt,
    withTools: [weatherTool]
)

print(response)
// The model calls WeatherTool and incorporates the result:
// "The weather in San Francisco is currently sunny with a temperature of 72°F and 45% humidity."
```

## Advanced Tool Examples

### Search Tool

```swift
struct SearchTool: Tool {
    static let description = "Searches the web for information on a given query"
    
    struct Arguments: Decodable {
        let query: String
        let maxResults: Int?
    }
    
    func call(arguments: Arguments) async throws -> String {
        let limit = arguments.maxResults ?? 5
        
        // Call search API (simplified)
        let results = try await performSearch(
            query: arguments.query,
            limit: limit
        )
        
        return results.map { result in
            "\(result.title): \(result.snippet) (\(result.url))"
        }.joined(separator: "\n\n")
    }
    
    private func performSearch(query: String, limit: Int) async throws -> [SearchResult] {
        // Implementation would call actual search API
        return []
    }
}

struct SearchResult {
    let title: String
    let snippet: String
    let url: String
}
```

### Database Query Tool

```swift
struct DatabaseQueryTool: Tool {
    static let description = "Queries the user database for information"
    
    struct Arguments: Decodable {
        let table: String
        let conditions: [String: String]
        let columns: [String]?
    }
    
    let database: Database
    
    func call(arguments: Arguments) async throws -> String {
        let columns = arguments.columns ?? ["*"]
        
        let results = try await database.query(
            table: arguments.table,
            columns: columns,
            where: arguments.conditions
        )
        
        return formatResults(results)
    }
    
    private func formatResults(_ results: [[String: Any]]) -> String {
        // Format database results as readable text
        return results.map { row in
            row.map { "\($0.key): \($0.value)" }.joined(separator: ", ")
        }.joined(separator: "\n")
    }
}
```

### Calculator Tool

```swift
struct CalculatorTool: Tool {
    static let description = "Performs mathematical calculations"
    
    struct Arguments: Decodable {
        let expression: String
    }
    
    func call(arguments: Arguments) async throws -> String {
        let result = try evaluateExpression(arguments.expression)
        return "Result: \(result)"
    }
    
    private func evaluateExpression(_ expression: String) throws -> Double {
        // Use NSExpression or implement custom parser
        let mathExpression = NSExpression(format: expression)
        guard let result = mathExpression.expressionValue(with: nil, context: nil) as? Double else {
            throw CalculatorError.invalidExpression
        }
        return result
    }
}

enum CalculatorError: Error {
    case invalidExpression
}
```

### File System Tool

```swift
struct FileSystemTool: Tool {
    static let description = "Lists files and directories in a specified path"
    
    struct Arguments: Decodable {
        let path: String
        let includeHidden: Bool?
    }
    
    func call(arguments: Arguments) async throws -> String {
        let fileManager = FileManager.default
        let showHidden = arguments.includeHidden ?? false
        
        let contents = try fileManager.contentsOfDirectory(atPath: arguments.path)
        let filtered = showHidden ? contents : contents.filter { !$0.hasPrefix(".") }
        
        return "Files in \(arguments.path):\n" + filtered.joined(separator: "\n")
    }
}
```

### API Request Tool

```swift
struct APIRequestTool: Tool {
    static let description = "Makes HTTP requests to external APIs"
    
    struct Arguments: Decodable {
        let url: String
        let method: String // "GET", "POST", etc.
        let headers: [String: String]?
        let body: String?
    }
    
    func call(arguments: Arguments) async throws -> String {
        guard let url = URL(string: arguments.url) else {
            throw APIError.invalidURL
        }
        
        var request = URLRequest(url: url)
        request.httpMethod = arguments.method
        
        if let headers = arguments.headers {
            for (key, value) in headers {
                request.setValue(value, forHTTPHeaderField: key)
            }
        }
        
        if let body = arguments.body {
            request.httpBody = body.data(using: .utf8)
        }
        
        let (data, response) = try await URLSession.shared.data(for: request)
        
        guard let httpResponse = response as? HTTPURLResponse,
              (200...299).contains(httpResponse.statusCode) else {
            throw APIError.requestFailed
        }
        
        return String(data: data, encoding: .utf8) ?? ""
    }
}

enum APIError: Error {
    case invalidURL
    case requestFailed
}
```

## Multiple Tools

You can provide multiple tools for the model to choose from:

```swift
let session = try await model.session()

let tools: [Tool] = [
    WeatherTool(),
    SearchTool(),
    CalculatorTool()
]

let prompt = Prompt {
    Instructions("You are a helpful assistant with access to various tools")
    "What's 15% of the temperature in Miami?"
}

let response = try await session.respond(to: prompt, withTools: tools)
// Model will:
// 1. Call WeatherTool for Miami
// 2. Call CalculatorTool to compute 15% of the temperature
// 3. Formulate a response with both results
```

## Tool Chaining

The model can call tools multiple times and chain results:

```swift
struct CurrencyConverterTool: Tool {
    static let description = "Converts currency amounts between different currencies"
    
    struct Arguments: Decodable {
        let amount: Double
        let from: String // Currency code (USD, EUR, etc.)
        let to: String
    }
    
    func call(arguments: Arguments) async throws -> String {
        let rate = try await getExchangeRate(from: arguments.from, to: arguments.to)
        let converted = arguments.amount * rate
        return "\(arguments.amount) \(arguments.from) = \(converted) \(arguments.to)"
    }
    
    private func getExchangeRate(from: String, to: String) async throws -> Double {
        // Call exchange rate API
        return 1.1 // Simplified
    }
}

let prompt = Prompt {
    Instructions("You help with travel planning")
    "I have $500 USD. What's that in EUR? Also, what's the weather like in Paris?"
}

let response = try await session.respond(
    to: prompt,
    withTools: [CurrencyConverterTool(), WeatherTool()]
)
// Model calls both tools and combines the information
```

## Error Handling in Tools

```swift
struct DatabaseTool: Tool {
    static let description = "Queries the database"
    
    struct Arguments: Decodable {
        let query: String
    }
    
    func call(arguments: Arguments) async throws -> String {
        do {
            let results = try await database.execute(arguments.query)
            return formatResults(results)
        } catch let error as DatabaseError {
            // Return user-friendly error message
            switch error {
            case .connectionFailed:
                return "Error: Unable to connect to database"
            case .invalidQuery:
                return "Error: Invalid query syntax"
            case .accessDenied:
                return "Error: Access denied to requested data"
            }
        }
    }
}
```

## Best Practices

### 1. Clear Tool Descriptions

```swift
// Good
struct EmailTool: Tool {
    static let description = "Sends an email to a specified recipient with a subject and body"
    // ...
}

// Less effective
struct EmailTool: Tool {
    static let description = "Email"
    // ...
}
```

### 2. Descriptive Argument Names

```swift
struct Arguments: Decodable {
    // Good
    let destinationEmail: String
    let messageSubject: String
    let messageBody: String
    
    // Less clear
    let to: String
    let subj: String
    let msg: String
}
```

### 3. Validate Arguments

```swift
func call(arguments: Arguments) async throws -> String {
    // Validate input
    guard arguments.email.contains("@") else {
        throw ToolError.invalidEmail
    }
    
    guard arguments.amount >= 0 else {
        throw ToolError.invalidAmount
    }
    
    // Proceed with tool logic
    // ...
}
```

### 4. Provide Useful Error Messages

```swift
func call(arguments: Arguments) async throws -> String {
    guard let data = try? await fetchData(arguments.id) else {
        return "Could not find data for ID \(arguments.id). Please check the ID and try again."
    }
    
    return formatData(data)
}
```

### 5. Return Structured Information

```swift
func call(arguments: Arguments) async throws -> String {
    let user = try await database.getUser(id: arguments.userId)
    
    return """
    User Information:
    - Name: \(user.name)
    - Email: \(user.email)
    - Status: \(user.status)
    - Last Login: \(user.lastLogin)
    """
}
```

### 6. Handle Rate Limiting

```swift
struct APITool: Tool {
    private let rateLimiter = RateLimiter(requestsPerSecond: 10)
    
    func call(arguments: Arguments) async throws -> String {
        try await rateLimiter.wait()
        
        // Make API request
        let result = try await makeRequest(arguments)
        return result
    }
}
```

### 7. Log Tool Usage

```swift
func call(arguments: Arguments) async throws -> String {
    logger.info("Tool called with arguments: \(arguments)")
    
    let result = try await performOperation(arguments)
    
    logger.info("Tool completed successfully")
    return result
}
```

## Security Considerations

### 1. Validate and Sanitize Input

```swift
func call(arguments: Arguments) async throws -> String {
    // Sanitize file paths
    let sanitized = arguments.path
        .replacingOccurrences(of: "..", with: "")
        .trimmingCharacters(in: .whitespaces)
    
    // Validate path is within allowed directory
    guard sanitized.hasPrefix(allowedDirectory) else {
        throw SecurityError.unauthorizedPath
    }
    
    // Proceed safely
    return try await readFile(at: sanitized)
}
```

### 2. Use Least Privilege

```swift
struct ReadOnlyDatabaseTool: Tool {
    // Only allow SELECT queries, not INSERT/UPDATE/DELETE
    func call(arguments: Arguments) async throws -> String {
        guard arguments.query.lowercased().hasPrefix("select") else {
            throw SecurityError.unauthorizedOperation
        }
        
        return try await database.execute(arguments.query)
    }
}
```

### 3. Implement Timeouts

```swift
func call(arguments: Arguments) async throws -> String {
    try await withTimeout(seconds: 30) {
        return try await longRunningOperation(arguments)
    }
}
```

## Testing Tools

```swift
// Unit test for a tool
func testWeatherTool() async throws {
    let tool = WeatherTool()
    let arguments = WeatherTool.Arguments(
        location: "San Francisco",
        units: "fahrenheit"
    )
    
    let result = try await tool.call(arguments: arguments)
    
    XCTAssertTrue(result.contains("San Francisco"))
    XCTAssertTrue(result.contains("°F"))
}

// Integration test with model
func testToolWithModel() async throws {
    let model = try await SystemLanguageModel()
    let session = try await model.session()
    
    let tool = WeatherTool()
    let prompt = Prompt(text: "What's the weather in Boston?")
    
    let response = try await session.respond(to: prompt, withTools: [tool])
    
    XCTAssertTrue(response.contains("Boston"))
}
```

## Common Patterns

### Tool Factory

```swift
struct ToolFactory {
    static func createTools(for context: AppContext) -> [Tool] {
        var tools: [Tool] = []
        
        if context.hasWeatherAccess {
            tools.append(WeatherTool())
        }
        
        if context.hasDatabaseAccess {
            tools.append(DatabaseQueryTool(database: context.database))
        }
        
        if context.hasSearchAccess {
            tools.append(SearchTool())
        }
        
        return tools
    }
}
```

### Tool Result Caching

```swift
actor ToolCache {
    private var cache: [String: (result: String, timestamp: Date)] = [:]
    private let cacheTimeout: TimeInterval = 300 // 5 minutes
    
    func getCached(for key: String) -> String? {
        guard let cached = cache[key],
              Date().timeIntervalSince(cached.timestamp) < cacheTimeout else {
            return nil
        }
        return cached.result
    }
    
    func cache(result: String, for key: String) {
        cache[key] = (result, Date())
    }
}

struct CachedWeatherTool: Tool {
    static let description = "Gets current weather information"
    private let cache = ToolCache()
    
    struct Arguments: Decodable {
        let location: String
    }
    
    func call(arguments: Arguments) async throws -> String {
        let cacheKey = arguments.location.lowercased()
        
        if let cached = await cache.getCached(for: cacheKey) {
            return cached
        }
        
        let result = try await fetchWeather(location: arguments.location)
        await cache.cache(result: result, for: cacheKey)
        
        return result
    }
}
```
