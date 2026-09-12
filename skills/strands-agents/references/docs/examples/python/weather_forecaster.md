# Weather Forecaster - Strands Agents HTTP Integration Example

This [example](https://github.com/strands-agents/docs/blob/main/docs/examples/python/weather_forecaster.py) demonstrates how to integrate the Strands Agents SDK with tool use, specifically using the `http_request` tool to build a weather forecasting agent that connects with the National Weather Service API. It shows how to combine natural language understanding with API capabilities to retrieve and present weather information.

## Overview

| Feature            | Description                            |
| ------------------ | -------------------------------------- |
| **Tool Used**      | http_request                           |
| **API**            | National Weather Service API (no key required) |
| **Complexity**     | Beginner                               |
| **Agent Type**     | Single agent                           |
| **Interaction**    | Command Line Interface                 |

## Tool Overview

The [`http_request`](https://github.com/strands-agents/tools/blob/main/src/strands_tools/http_request.py) tool enables Strands agents to connect with external web services and APIs, connecting conversational AI with data sources. This tool supports multiple HTTP methods (GET, POST, PUT, DELETE), handles URL encoding and response parsing, and returns structured data from web sources.

## Code Structure and Implementation

The example demonstrates how to integrate the Strands Agents SDK with tools to create an intelligent weather agent:

### Creating the Weather Agent

```python
from strands import Agent
from strands_tools import http_request

# Define a weather-focused system prompt
WEATHER_SYSTEM_PROMPT = """You are a weather assistant with HTTP capabilities. You can:

1. Make HTTP requests to the National Weather Service API
2. Process and display weather forecast data
3. Provide weather information for locations in the United States

When retrieving weather information:
1. First get the coordinates or grid information using https://api.weather.gov/points/{latitude},{longitude} or https://api.weather.gov/points/{zipcode}
2. Then use the returned forecast URL to get the actual forecast

When displaying responses:
- Format weather data in a human-readable way
- Highlight important information like temperature, precipitation, and alerts
- Handle errors appropriately
- Convert technical terms to user-friendly language

Always explain the weather conditions clearly and provide context for the forecast.
"""

# Create an agent with HTTP capabilities
weather_agent = Agent(
    system_prompt=WEATHER_SYSTEM_PROMPT,
    tools=[http_request],  # Explicitly enable http_request tool
)
```

The system prompt is crucial as it:

- Defines the agent's purpose and capabilities
- Outlines the multi-step API workflow
- Specifies response formatting expectations
- Provides domain-specific instructions

### Using the Weather Agent

The weather agent can be used in two primary ways:

#### 1. Natural Language Instructions

Natural language interaction provides flexibility, allowing the agent to understand user intent and select the appropriate tool actions based on context. Users can interact with the National Weather Service API through conversational queries:

```python
# Let the agent handle the API details
response = weather_agent("What's the weather like in Seattle?")
response = weather_agent("Will it rain tomorrow in Miami?")
response = weather_agent("Compare the temperature in New York and Chicago this weekend")
```

#### Multi-Step API Workflow Behind the Scenes

When a user asks a weather question, the agent handles a multi-step process:

##### Step 1: Location Information Request
The agent:

- Makes an HTTP GET request to `https://api.weather.gov/points/{latitude},{longitude}` or `https://api.weather.gov/points/{zipcode}`
- Extracts key properties from the response JSON:
  - `properties.forecast`: URL for the forecast data
  - `properties.forecastHourly`: URL for hourly forecast data
  - `properties.relativeLocation`: Information about the nearest location name
  - `properties.gridId`, `properties.gridX`, `properties.gridY`: Grid identifiers

##### Step 2: Forecast Data Request
The agent then:

- Uses the extracted forecast URL to make a second HTTP request
- Processes the `properties.periods` array containing forecast periods with data like:
  - `temperature` and `temperatureUnit`
  - `windSpeed` and `windDirection`
  - `shortForecast` and `detailedForecast` descriptions
  - Timing information (`startTime`, `endTime`, `isDaytime`)

##### Step 3: Natural Language Processing
The agent transforms this technical data into conversational responses by:

- Prioritizing relevant information based on the user's question
- Converting technical terms to user-friendly language
- Formatting the response in a readable structure
- Adding context and recommendations when appropriate


#### 2. Direct Tool Calls

For developers requiring programmatic control, Strands also supports direct method calls to the same API. This approach provides explicit control and is recommended for scenarios that benefit from predictable execution, such as API integrations with validation or transformation, database operations, or payment processing.

```python
# Direct API method calls with Strands
location_response = weather_agent.tool.http_request(
    method="GET",
    url="https://api.weather.gov/points/47.6062,-122.3321"  # Seattle coordinates
)

# Process response as needed
import json
location_data = json.loads(location_response['body'])
forecast_url = location_data.get('properties', {}).get('forecast')

# Make a second request to get the forecast
forecast_response = weather_agent.tool.http_request(
    method="GET",
    url=forecast_url
)
```
### Sample Queries and Responses

**Query 1**: What's the weather like in Seattle?

**Response**:
```
Current weather in Seattle, WA:
Temperature: 52°F
Conditions: Partly Sunny
Wind: NW at 8 mph
Humidity: 68%

Today's forecast: Partly sunny with a high near 55°F. Northwest wind around 8 mph.
```

**Query 2**: Will it rain tomorrow in Miami?

**Response**:
```
Tomorrow's forecast for Miami, FL:
There is a 30% chance of showers, mainly after 2pm.
Otherwise, it will be mostly sunny with a high near 84°F.
Southeast wind 5 to 9 mph.

Rain is possible but not highly likely for tomorrow.
```

## Extending the Example

Here are some ways you could extend this weather forecaster example:

1. **Add location search**: Implement geocoding to convert city names to coordinates
2. **Support more weather data**: Add hourly forecasts, alerts, or radar images
3. **Improve response formatting**: Create better formatted weather reports
4. **Add caching**: Implement caching to reduce API calls for frequent locations
5. **Create a web interface**: Build a web UI for the weather agent
