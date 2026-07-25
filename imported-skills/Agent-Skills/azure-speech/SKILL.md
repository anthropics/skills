---
name: azure-speech
description: Expert knowledge for Azure AI Speech development including troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when building STT/TTS containers, custom voices, Voice Live apps, SSML workflows, or telephony integrations, and other Azure AI Speech related development tasks. Not for Azure AI Bot Service (use azure-bot-service), Azure Communication Services (use azure-communication-services), Azure AI Immersive Reader (use azure-immersive-reader), Azure Translator (use azure-translator).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure AI Speech Skill

This skill provides expert guidance for Azure AI Speech. Covers troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L44 | Diagnosing and resolving Azure AI Speech issues: session/ID lookup, Foundry integration errors, SDK CRL/compatibility problems, container deployment failures, and common SDK runtime bugs. |
| Best Practices | L45-L60 | Guidance on preparing audio/video data, improving transcription and synthesis quality/latency, designing microphones, managing SDK memory, handling live voice chats, and backing up custom voice resources. |
| Decision Making | L61-L77 | Guides for choosing Azure Speech/Embedded/Voice Live options, checking language/voice availability, and step-by-step migrations between Speech/voice REST APIs and legacy features. |
| Limits & Quotas | L78-L86 | Speech service limits, quotas, and behaviors for text-to-speech and custom/professional voice models, including training duration, deployment constraints, and managing model/endpoint lifecycles. |
| Security | L87-L100 | Securing Azure AI Speech: auth (Entra, RBAC), network isolation (VNet, Private Link, sovereign clouds), encryption/BYOK, BYOS storage, and consent/ID flows for personal and professional voice. |
| Configuration | L101-L133 | Configuring Azure AI Speech behavior: audio I/O, logging, storage, SSML, pronunciation, batch TTS/STT, avatars, personal/pro voices, and Voice Live/SDK/CLI connection and telemetry settings. |
| Integrations & Coding Patterns | L134-L164 | Patterns and code for integrating Azure Speech/Voice Live with apps, telephony, agents, REST/SDK/WS APIs, TTS/translation/avatars, SSML customization, and LLM/OpenAI workflows. |
| Deployment | L165-L176 | Deploying and scaling Azure AI Speech: Docker/Kubernetes containers, on-prem STT/TTS, custom speech models/endpoints, language ID, and batch/long-form synthesis workflows. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Retrieve Speech to text session and transcription IDs for support | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-get-speech-session-id |
| Resolve common Azure Speech in Foundry issues | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/known-issues |
| Resolve Azure AI Speech SDK CRL compatibility issues | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/migrate-to-sdk-1-48-2 |
| Troubleshoot Azure Speech containers deployment issues | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-container-faq |
| Diagnose and fix common Azure Speech SDK issues | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/troubleshooting |

### Best Practices
| Topic | URL |
|-------|-----|
| Prepare and locate audio data for batch transcription | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/batch-transcription-audio-data |
| Create high-quality human-labeled speech transcriptions | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-custom-speech-human-labeled-transcriptions |
| Prepare training data for professional custom voice | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-custom-voice-training-data |
| Apply best practices to reduce Speech synthesis latency | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-lower-speech-synthesis-latency |
| Track and manage Azure Speech SDK memory usage | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-track-speech-sdk-memory-usage |
| Handle interrupted responses in Voice Live chat history | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-voice-live-auto-truncation |
| Use phrase lists to improve Azure Speech accuracy | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/improve-accuracy-phrase-list |
| Apply keyword recognition design and accuracy guidelines | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/keyword-recognition-guidelines |
| Record high-quality samples for custom voice training | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/record-custom-voice-samples |
| Back up and recover custom Speech and Voice resources | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/resiliency-and-recovery-plan |
| Design microphone arrays optimized for Speech SDK | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-sdk-microphone |
| Prepare high-quality video samples for custom avatars | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/text-to-speech-avatar/custom-avatar-record-video-samples |

### Decision Making
| Topic | URL |
|-------|-----|
| Evaluate custom voice lite before professional voice | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/custom-neural-voice-lite |
| Choose Embedded Speech for offline and hybrid scenarios | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/embedded-speech |
| Evaluate device suitability for embedded speech models | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/embedded-speech-performance-evaluations |
| Check Azure Speech language and voice availability | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/language-support |
| Migrate Speech to text REST API from v3.2 to 2024-11-15 | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/migrate-2024-11-15 |
| Migrate Speech to text REST API 2024-11-15 to 2025-10-15 | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/migrate-2025-10-15 |
| Migrate from retired Speech intent recognition to Language or OpenAI | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/migrate-intent-recognition |
| Migrate from Long Audio API to Batch synthesis | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/migrate-to-batch-synthesis |
| Migrate from v3 text-to-speech to custom voice REST API | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/migrate-to-custom-voice-api |
| Migrate Speech-to-text REST from v3.0 to v3.1 | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/migrate-v3-0-to-v3-1 |
| Migrate Speech to text REST API v3.1 to v3.2 | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/migrate-v3-1-to-v3-2 |
| Assess capabilities and regions for personal voice | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/personal-voice-overview |
| Select models and pricing for Voice Live API | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/voice-live |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Text to speech FAQs including limits and behavior | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/faq-tts |
| Manage custom speech model and endpoint lifecycle | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-custom-speech-model-and-endpoint-lifecycle |
| Deploy professional voice models to custom endpoints | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/professional-voice-deploy-endpoint |
| Train professional voice models and understand duration | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/professional-voice-train-voice |
| Reference quotas and limits for Azure Speech | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-services-quotas-and-limits |

### Security
| Topic | URL |
|-------|-----|
| Configure BYOS storage for Azure Speech resources | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/bring-your-own-storage-speech-resource |
| Configure Microsoft Entra authentication for Speech SDK | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-configure-azure-ad-auth |
| Configure consent requirements for personal voice projects | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/personal-voice-create-consent |
| Create personal voice projects with consent and IDs | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/personal-voice-create-project |
| Add and manage voice talent consent for professional voice | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/professional-voice-create-consent |
| Assign Azure RBAC roles for Speech resources | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/role-based-access-control |
| Configure Speech service in Azure sovereign clouds | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/sovereign-clouds |
| Manage Speech service data-at-rest encryption and keys | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-encryption-of-data-at-rest |
| Secure Speech service with Virtual Network service endpoints | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-service-vnet-service-endpoint |
| Secure Azure AI Speech with Private Link endpoints | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-services-private-link |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Batch synthesis properties for text-to-speech | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/batch-synthesis-properties |
| Check status and retrieve batch transcription results | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/batch-transcription-get |
| Configure BYOS storage for Speech to text | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/bring-your-own-storage-speech-resource-speech-to-text |
| Define UPS phonetic pronunciations for Speech to text | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/customize-pronunciation |
| Configure OpenSSL on Linux for Azure Speech SDK | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-configure-openssl-linux |
| Control and monitor Speech SDK service connections | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-control-connections |
| Select and configure audio input devices in Speech SDK | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-select-audio-input-devices |
| Use visemes for facial animation with Speech service | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-speech-synthesis-viseme |
| Configure Speech SDK audio input streams | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-use-audio-input-streams |
| Configure compressed audio input for Speech SDK and CLI | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-use-codec-compressed-audio-input-streams |
| Enable and configure Speech SDK diagnostic logging | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-use-logging |
| Configure interim responses for Voice Live latency | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-voice-live-interim-response |
| Configure OpenTelemetry tracing for Voice Live SDK | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-voice-live-telemetry |
| Configure audio and transcription logging for Speech recognition | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/logging-audio-transcription |
| Create and manage personal voice speaker profiles | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/personal-voice-create-voice |
| Upload and validate training datasets for professional voice | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/professional-voice-create-training-set |
| Configure Azure Speech text-to-speech avatar options | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/quickstarts/get-started-text-to-speech-avatar |
| Use correct Azure Speech regional endpoints | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/regions |
| Configure Speech containers storage, logging, and security | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-container-configuration |
| Control speech output using SSML configuration | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-synthesis-markup |
| Configure pronunciation with SSML phonemes and lexicons | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-synthesis-markup-pronunciation |
| Structure SSML documents and events for Speech | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-synthesis-markup-structure |
| Configure Speech CLI datastore search order and files | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/spx-data-store-configuration |
| Configure output destinations for Speech CLI results | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/spx-output-options |
| Configure batch synthesis properties for TTS avatars | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/text-to-speech-avatar/batch-synthesis-avatar-properties |
| Reference Voice Live API events, models, and settings (2025-10-01) | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/voice-live-api-reference-2025-10-01 |
| Reference Voice Live API events and settings (2026-01-01-preview) | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/voice-live-api-reference-2026-01-01-preview |
| Configure Voice Live WebSocket events and settings | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/voice-live-how-to |
| Configure language and locale support in Voice Live | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/voice-live-language-support |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Speech service with call center telephony | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/call-center-telephony-integration |
| Call Azure Speech fast transcription API in Foundry | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/fast-transcription-create |
| Use Speech SDK APIs to handle recognition results | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/get-speech-recognition-results |
| Integrate custom models with Voice Live API (BYOM) | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-bring-your-own-model |
| Implement text-to-speech synthesis with Speech SDK | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-speech-synthesis |
| Implement speech translation with Azure Speech SDK | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-translate-speech |
| Integrate Voice Live with Foundry Agent Service | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-voice-agent-integration |
| Implement function calling in Voice Live sessions | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-voice-live-function-calling |
| Integrate Voice Live with Foundry hosted agents | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-voice-live-hosted-agent-integration |
| Connect MCP servers to Voice Live sessions | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-voice-live-mcp-server |
| Add proactive greeting messages to Voice Live agents | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-voice-live-proactive-messages |
| Use Azure LLM Speech API for transcription | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/llm-speech |
| Use MAI-Transcribe with LLM Speech API | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/mai-transcribe |
| Integrate Azure Speech with Azure OpenAI chat | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/openai-speech |
| Integrate Azure Personal Voice into applications | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/personal-voice-how-to-use |
| Use Power Automate connector for Speech batch transcription | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/power-automate-batch-transcription |
| Use Speech to text REST API endpoints and parameters | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/rest-speech-to-text |
| Call Azure Speech-to-text short audio REST API | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/rest-speech-to-text-short |
| Call Speech text to speech REST API endpoints | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/rest-text-to-speech |
| Use SSML phonetic alphabets with Azure Speech | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-ssml-phonetic-sets |
| Use SSML to customize Azure Speech voices | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-synthesis-markup-voice |
| Generate Speech service REST clients from Swagger | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/swagger-documentation |
| Control text to speech avatar gestures with SSML | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/text-to-speech-avatar/avatar-gestures-with-ssml |
| Implement real-time text-to-speech avatar streaming | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/text-to-speech-avatar/real-time-synthesis-avatar |
| Use Voice Live WebSocket API events and models | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/voice-live-api-reference-2026-04-10 |
| Integrate with Voice Live preview WebSocket API | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/voice-live-api-reference-2026-06-01-preview |
| Integrate Voice Live API with telephony systems | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/voice-live-telephony |

### Deployment
| Topic | URL |
|-------|-----|
| Use Batch synthesis API for long-form text-to-speech | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/batch-synthesis |
| Deploy custom speech models and endpoints | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/how-to-custom-speech-deploy-model |
| Scale Speech containers with batch processing kit | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-container-batch-processing |
| Run custom speech to text containers with Docker | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-container-cstt |
| Deploy and run Speech containers with Docker | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-container-howto |
| Run Speech containers on Kubernetes with Helm | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-container-howto-on-premises |
| Deploy language identification containers with Docker | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-container-lid |
| Deploy neural text to speech containers with Docker | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-container-ntts |
| Deploy speech to text containers for on-premises use | https://learn.microsoft.com/en-us/azure/ai-services/speech-service/speech-container-stt |