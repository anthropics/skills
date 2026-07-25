---
name: azure-maps
description: Expert knowledge for Azure Maps development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and integrations & coding patterns. Use when using web/REST/Power BI SDKs, geocoding/routing/weather APIs, tiles/rendering, or DEM/cuOpt routing, and other Azure Maps related development tasks. Not for Azure AI Search (use azure-cognitive-search), Azure IoT (use azure-iot), Azure IoT Central (use azure-iot-central), Azure IoT Edge (use azure-iot-edge).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Maps Skill

This skill provides expert guidance for Azure Maps. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L40 | Diagnosing and fixing common Azure Maps Weather API issues, including authentication, quota/usage limits, request/response errors, and troubleshooting incorrect or missing weather data. |
| Best Practices | L41-L51 | Best practices for Azure Maps apps: auth/security, routing and search usage, static image rendering, performance tuning, accessibility, and correct copyright/attribution. |
| Decision Making | L52-L63 | Guidance on pricing, billing, and migrating maps apps to Azure Maps from Bing, Google, Power BI visuals, and older Azure Maps APIs, including routing, tiles, and search replacements |
| Architecture & Design Patterns | L64-L69 | Designing Azure architectures for elevation data services and multi-itinerary route optimization using Azure Maps, open DEM data, and NVIDIA cuOpt for scalable geospatial solutions |
| Limits & Quotas | L70-L79 | Coverage, limits, and capabilities of Azure Maps services: QPS rate limits, and regional support for geocoding, rendering/tiles, routing, traffic, and weather data. |
| Security | L80-L94 | Securing Azure Maps access: auth methods (keys, SAS, Entra ID), SPA/daemon/device scenarios, Power BI visual governance, and network isolation with Private Link. |
| Configuration | L95-L119 | Configuring Azure Maps web maps, styles, layers, data sources, routing models, localization, browser support, and migrating or updating to newer Azure Maps APIs and services. |
| Integrations & Coding Patterns | L120-L181 | Patterns and code for integrating Azure Maps: Web/REST/Power BI SDK usage, layers and drawing, geocoding/routing/weather, Spatial IO/WMS, and migrations from Bing/Google/legacy SDKs. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Azure Maps Weather service issues | https://learn.microsoft.com/en-us/azure/azure-maps/weather-services-faq |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply authentication best practices for Azure Maps apps | https://learn.microsoft.com/en-us/azure/azure-maps/authentication-best-practices |
| Render custom data on Azure Maps static raster images | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-render-custom-data |
| Show required Azure Maps copyright attribution correctly | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-show-attribution |
| Apply best practices for Azure Maps Route service | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-use-best-practices-for-routing |
| Apply best practices for Azure Maps Search | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-use-best-practices-for-search |
| Implement accessibility features in Azure Maps apps | https://learn.microsoft.com/en-us/azure/azure-maps/map-accessibility |
| Optimize performance with Azure Maps Web SDK best practices | https://learn.microsoft.com/en-us/azure/azure-maps/web-sdk-best-practices |

### Decision Making
| Topic | URL |
|-------|-----|
| Select and manage Azure Maps pricing tiers | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-manage-pricing-tier |
| Plan migration from Bing Maps Enterprise to Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-bing-maps-overview |
| Migrate Bing Truck Route API to Azure Maps routing | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-calculate-truck-route |
| Decide how to migrate from Google Maps to Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-from-google-maps |
| Migrate Bing Get Imagery Metadata to Azure Maps tiles | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-get-imagery-metadata |
| Choose Azure Maps and Azure services to replace Bing SDS | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-sds-data-source-management |
| Convert Power BI Map visuals to Azure Maps visual | https://learn.microsoft.com/en-us/azure/azure-maps/power-bi-visual-conversion |
| Interpret Azure Maps transaction billing and usage | https://learn.microsoft.com/en-us/azure/azure-maps/understanding-azure-maps-transactions |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Build elevation data services on Azure using open DEM data | https://learn.microsoft.com/en-us/azure/azure-maps/elevation-data-services |
| Architect a multi-itinerary optimization service with Azure Maps and NVIDIA cuOpt | https://learn.microsoft.com/en-us/azure/azure-maps/itinerary-optimization-service |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Azure Maps QPS rate limits by pricing tier | https://learn.microsoft.com/en-us/azure/azure-maps/azure-maps-qps-rate-limits |
| Check Azure Maps geocoding coverage by region | https://learn.microsoft.com/en-us/azure/azure-maps/geocoding-coverage |
| Understand Azure Maps render coverage and tile detail | https://learn.microsoft.com/en-us/azure/azure-maps/render-coverage |
| Evaluate Azure Maps routing coverage and capabilities | https://learn.microsoft.com/en-us/azure/azure-maps/routing-coverage |
| Review Azure Maps traffic data coverage worldwide | https://learn.microsoft.com/en-us/azure/azure-maps/traffic-coverage |
| Check Azure Maps weather service regional coverage | https://learn.microsoft.com/en-us/azure/azure-maps/weather-coverage |

### Security
| Topic | URL |
|-------|-----|
| Configure Azure Maps authentication methods securely | https://learn.microsoft.com/en-us/azure/azure-maps/azure-maps-authentication |
| Configure authentication methods for Azure Maps accounts | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-manage-authentication |
| Secure Azure Maps daemon and background applications | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-secure-daemon-app |
| Secure input-constrained devices using Entra ID and Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-secure-device-code |
| Secure Azure Maps with SAS token authentication | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-secure-sas-app |
| Secure non-interactive SPAs for Azure Maps with Entra ID | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-secure-spa-app |
| Secure Azure Maps SPA with interactive user sign-in | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-secure-spa-users |
| Secure Azure Maps web apps with interactive sign-in | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-secure-webapp-users |
| Understand Azure Maps Power BI visual data residency behavior | https://learn.microsoft.com/en-us/azure/azure-maps/power-bi-visual-data-residency |
| Manage organizational access to Azure Maps Power BI visual | https://learn.microsoft.com/en-us/azure/azure-maps/power-bi-visual-manage-access |
| Secure Azure Maps access using Private Link endpoints | https://learn.microsoft.com/en-us/azure/azure-maps/private-endpoints |

### Configuration
| Topic | URL |
|-------|-----|
| Configure map styles in Azure Maps Web Map Control | https://learn.microsoft.com/en-us/azure/azure-maps/choose-map-style |
| Configure vehicle consumption models in Azure Maps routing | https://learn.microsoft.com/en-us/azure/azure-maps/consumption-model |
| Create and manage data sources in Azure Maps Web SDK | https://learn.microsoft.com/en-us/azure/azure-maps/create-data-source-web-sdk |
| Use Azure Maps extended GeoJSON geometries | https://learn.microsoft.com/en-us/azure/azure-maps/extend-geojson |
| Provision Azure Maps accounts using ARM templates | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-create-template |
| Configure Azure Maps global data processing regions | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-manage-consent |
| Add and configure Bubble layers in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-bubble-layer |
| Configure controls on Azure Maps Web maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-controls |
| Add HTML markers and events to Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-custom-html |
| Add and configure Symbol layers in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-pin |
| Add and customize popups on Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-popup |
| Migrate Azure Maps Route v1.0 APIs to 2025-01-01 | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-route-v1-api |
| Migrate Azure Maps Traffic v1 service to newer APIs | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-traffic-v1-api |
| Supported spatial formats in Azure Maps Spatial IO | https://learn.microsoft.com/en-us/azure/azure-maps/spatial-io-read-write-spatial-data |
| Delimited and XML spatial data parsing rules in Spatial IO | https://learn.microsoft.com/en-us/azure/azure-maps/spatial-io-supported-data-format-details |
| Browser support and feature detection for Azure Maps Web SDK | https://learn.microsoft.com/en-us/azure/azure-maps/supported-browsers |
| Configure Azure Maps localization languages and views | https://learn.microsoft.com/en-us/azure/azure-maps/supported-languages |
| Select and use built-in Azure Maps map styles | https://learn.microsoft.com/en-us/azure/azure-maps/supported-map-styles |
| Use Azure Maps supported search category codes | https://learn.microsoft.com/en-us/azure/azure-maps/supported-search-categories |
| Migrate Azure Maps Web SDK apps from v1/v2 to v3 | https://learn.microsoft.com/en-us/azure/azure-maps/web-sdk-migration-guide |
| Configure Azure Maps zoom levels and tile coordinates | https://learn.microsoft.com/en-us/azure/azure-maps/zoom-levels-and-tile-grid |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use PMTiles custom protocol with Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/add-custom-protocol-pmtiles |
| Migrate Azure Maps Android SDK apps to Web SDK | https://learn.microsoft.com/en-us/azure/azure-maps/android-sdk-migration-guide |
| Integrate Azure Maps geofence events with Event Grid | https://learn.microsoft.com/en-us/azure/azure-maps/azure-maps-event-grid-integration |
| Cluster point data with Azure Maps Web SDK | https://learn.microsoft.com/en-us/azure/azure-maps/clustering-point-data-web-sdk |
| Use data-driven style expressions in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/data-driven-style-expressions-web-sdk |
| Use Azure Maps drawing tools events | https://learn.microsoft.com/en-us/azure/azure-maps/drawing-tools-events |
| Use drawing interactions and shortcuts in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/drawing-tools-interactions-keyboard-shortcuts |
| Integrate Azure Maps using the C# REST SDK | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-dev-guide-csharp-sdk |
| Integrate Azure Maps using the Java REST SDK | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-dev-guide-java-sdk |
| Integrate Azure Maps using the JavaScript REST SDK | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-dev-guide-js-sdk |
| Integrate Azure Maps using the Python REST SDK | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-dev-guide-py-sdk |
| Request real-time and forecast weather data with Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-request-weather-data |
| Use Azure Maps Search APIs for geocoding and POI lookup | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-search-for-address |
| Use image templates and fill patterns in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-use-image-templates-web-sdk |
| Use Azure Maps Web Map Control in web and mobile apps | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-use-map-control |
| Embed Azure Maps map control via npm in Node.js apps | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-use-npm-package |
| Integrate spatial data using Azure Maps Spatial IO | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-use-spatial-io-module |
| Use Azure Maps TypeScript REST SDK modules | https://learn.microsoft.com/en-us/azure/azure-maps/how-to-use-ts-rest-sdk |
| Migrate Azure Maps iOS SDK apps to Web SDK | https://learn.microsoft.com/en-us/azure/azure-maps/ios-sdk-migration-guide |
| Add and customize drawing toolbar in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-drawing-toolbar |
| Create and customize heat map layers in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-heat-map-layer |
| Overlay image layers on Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-image-layer |
| Render line layers with Azure Maps Web SDK | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-line-layer |
| Render polygon and circle layers in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-shape |
| Add and configure snap grid in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-snap-grid |
| Add tile layers and overlays in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-add-tile-layer |
| Create and animate maps with Azure Maps Web SDK | https://learn.microsoft.com/en-us/azure/azure-maps/map-create |
| Handle Azure Maps Web SDK map events | https://learn.microsoft.com/en-us/azure/azure-maps/map-events |
| Use polygon extrusion layers in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-extruded-polygon |
| Perform reverse geocoding in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-get-information-from-coordinate |
| Extract GeoJSON from drawn shapes in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-get-shape-data |
| Request and display routes with Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-route |
| Search locations and show results in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-search-location |
| Display traffic flow and incidents in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/map-show-traffic |
| Translate Bing route calculation to Azure Maps routing | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-calculate-route |
| Convert Bing address geocoding to Azure Maps Geocoding | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-find-location-address |
| Migrate Bing reverse geocoding to Azure Maps API | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-find-location-by-point |
| Migrate Bing query-based geocoding to Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-find-location-query |
| Migrate Bing time zone lookups to Azure Maps timezone API | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-find-time-zone |
| Migrate Bing Maps web apps to Azure Maps Web SDK | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-from-bing-maps-web-app |
| Migrate a web app from Google Maps to Azure Maps Web SDK | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-from-google-maps-web-app |
| Migrate Google Maps web services to Azure Maps REST APIs | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-from-google-maps-web-services |
| Migrate Bing Geocode Dataflow to Azure batch geocoding | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-geocode-dataflow |
| Replace Bing Geodata API with Azure Maps Get Polygon | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-geodata |
| Migrate Bing Static Map calls to Azure Static Image | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-get-static-map |
| Migrate Bing traffic incidents to Azure Maps incident details | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-get-traffic-incidents |
| Migrate Azure Maps Search v1 integrations to 2026-01-01 | https://learn.microsoft.com/en-us/azure/azure-maps/migrate-search-v1-api |
| Add and configure marker layers in Azure Maps visual | https://learn.microsoft.com/en-us/azure/azure-maps/power-bi-visual-add-marker-layer |
| Add pie chart layers in Azure Maps Power BI visual | https://learn.microsoft.com/en-us/azure/azure-maps/power-bi-visual-add-pie-chart-layer |
| Use cluster bubble layers in Azure Maps visual | https://learn.microsoft.com/en-us/azure/azure-maps/power-bi-visual-cluster-bubbles |
| Use geocoding in Azure Maps Power BI visual | https://learn.microsoft.com/en-us/azure/azure-maps/power-bi-visual-geocode |
| Get started with Azure Maps visual in Power BI | https://learn.microsoft.com/en-us/azure/azure-maps/power-bi-visual-get-started |
| Configure layers in Azure Maps Power BI visual | https://learn.microsoft.com/en-us/azure/azure-maps/power-bi-visual-understanding-layers |
| Configure Azure Maps drawing tools module | https://learn.microsoft.com/en-us/azure/azure-maps/set-drawing-options |
| Overlay OGC WMS/WMTS layers in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/spatial-io-add-ogc-map-layer |
| Render data with Spatial IO SimpleDataLayer | https://learn.microsoft.com/en-us/azure/azure-maps/spatial-io-add-simple-data-layer |
| Connect Azure Maps Spatial IO to WFS services | https://learn.microsoft.com/en-us/azure/azure-maps/spatial-io-connect-wfs-service |
| Use core CSV/XML IO operations in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/spatial-io-core-operations |
| Implement custom WebGL layers in Azure Maps | https://learn.microsoft.com/en-us/azure/azure-maps/webgl-custom-layer |