---
name: azure-communication-services
description: Expert knowledge for Azure Communication Services development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when building ACS calling, chat, SMS, email, Teams interop, or contact center/Job Router solutions, and other Azure Communication Services related development tasks. Not for Azure Notification Hubs (use azure-notification-hubs), Azure Web PubSub (use azure-web-pubsub), Azure SignalR Service (use azure-signalr-service), Azure AI Bot Service (use azure-bot-service).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure Communication Services Skill

This skill provides expert guidance for Azure Communication Services. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L111 | Diagnosing and fixing ACS calling, SMS, email, Teams, PSTN, audio/video, device, network, and SDK issues, plus collecting logs, UFD events, and diagnostics for support. |
| Best Practices | L112-L137 | Best practices for ACS calling, SMS, email, IDs, auth, Teams interop, network/quality, spam/opt-out compliance, and production-ready virtual visit and meeting experiences. |
| Decision Making | L138-L153 | Guidance on ACS/Teams design decisions: PSTN options and pricing, phone numbers, Teams interop and licensing, gov cloud usage, and migrating from Twilio Video/Chat to ACS. |
| Architecture & Design Patterns | L154-L159 | Designing scalable contact center solutions with ACS and patterns for integrating ACS with ExpressRoute for secure, private connectivity and network architecture. |
| Limits & Quotas | L160-L227 | Limits, quotas, regional availability, and restrictions for ACS calling, phone numbers, email, Teams interop, media features, and troubleshooting token/metric-related issues. |
| Security | L228-L254 | Security, auth, and compliance for ACS: encryption, identities, HMAC, caller ID, email/SMTP, Teams interop, captions/transcription, emergency calling, and secure webhooks/Rooms. |
| Configuration | L255-L332 | Monitoring, logging, metrics, and diagnostics for ACS (chat, voice/video, SMS, email, calling, routing), plus configuration for Teams interop, domains, routing, UI library, and SMS/email compliance. |
| Integrations & Coding Patterns | L333-L479 | Patterns and code to integrate ACS calling, chat, SMS, email, Rooms, Job Router, and WhatsApp with apps, bots, Teams, OpenAI, push/events, media, and telephony features. |
| Deployment | L480-L484 | Infrastructure and deployment guidance for Azure Communication Services: direct routing requirements and automating ACS/Email resource provisioning with PowerShell. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Use Job Router operational logs for diagnostics | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/router-logs |
| Troubleshoot ACS email custom domain configuration issues | https://learn.microsoft.com/en-us/azure/communication-services/concepts/email/email-domain-configuration-troubleshooting |
| Monitor logs and metrics for ACS Teams external users | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/guest/monitor-logs-metrics |
| Troubleshoot common Teams Phone extensibility issues with ACS | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/tpe/teams-phone-extensibility-troubleshooting |
| Resolve common Azure SMS questions and issues | https://learn.microsoft.com/en-us/azure/communication-services/concepts/sms/sms-faq |
| Troubleshoot ACS direct routing outbound call failures | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/monitoring-troubleshooting-telephony/troubleshoot-outbound-calls |
| Fix ACS direct routing TLS certificate and SIP OPTIONS issues | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/monitoring-troubleshooting-telephony/troubleshoot-tls-certificate-sip-options |
| Troubleshoot ACS PSTN call failures using result codes | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/troubleshooting-pstn-call-failures |
| Collect troubleshooting information for Azure Communication Services | https://learn.microsoft.com/en-us/azure/communication-services/concepts/troubleshooting-info |
| Use ACS Call Diagnostics to investigate call issues | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/call-diagnostics |
| Diagnose Azure Communication Services call quality issues | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/call-diagnostics |
| Review known issues in ACS native calling SDKs | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/known-issues-native |
| Review known issues for ACS WebJS calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/known-issues-webjs |
| Diagnose and fix ACS web VoIP call quality issues | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/troubleshoot-web-voip-quality |
| Use User Facing Diagnostics to detect ACS call issues | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/user-facing-diagnostics |
| Troubleshoot ACS UI Library calls and collect debug info | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/troubleshooting |
| Troubleshoot Azure-linked WhatsApp Business accounts | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/advanced-messaging/whatsapp/whatsapp-business-account-faq |
| Resolve audio delay issues in ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/audio-issues/delay-issue |
| Fix echo problems in ACS audio calls | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/audio-issues/echo-issue |
| Troubleshoot low incoming audio volume in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/audio-issues/incoming-audio-low-volume |
| Resolve one-way audio from faulty microphones in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/audio-issues/microphone-issue |
| Fix one-way audio when microphone permission is denied | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/audio-issues/microphone-permission |
| Handle one-way audio caused by network issues in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/audio-issues/network-issue |
| Diagnose ACS audio issues using UFD and device checks | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/audio-issues/overview |
| Diagnose poor audio quality in ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/audio-issues/poor-quality |
| Resolve one-way audio from speaker issues in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/audio-issues/speaker-issue |
| Fix ACS calls ending with 410/3112 network errors | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/call-setup-issues/call-ends-with-410-3112 |
| Resolve long ACS call setup times | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/call-setup-issues/call-setup-takes-too-long |
| Fix ACS CallAgent creation failures in Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/call-setup-issues/failed-to-create-call-agent |
| Troubleshoot missing incoming call notifications in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/call-setup-issues/no-incoming-call-notifications |
| Identify stages of ACS call setup issues | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/call-setup-issues/overview |
| Troubleshoot slow askDevicePermission responses in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/device-issues/ask-device-permission-api-takes-too-long |
| Fix missing detailed microphone list in ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/device-issues/no-enumerated-microphone-list |
| Fix missing detailed speaker list in ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/device-issues/no-enumerated-speaker-list |
| Resolve missing permission prompts in ACS device access | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/device-issues/no-permission-prompt |
| Understand ACS device and permission issues in calls | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/device-issues/overview |
| Apply general troubleshooting strategies for ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/general-troubleshooting-strategies/overview |
| Report unresolved ACS calling issues effectively | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/general-troubleshooting-strategies/report-issue |
| Interpret ACS Calling SDK error messages and codes | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/general-troubleshooting-strategies/understanding-error-codes |
| Collect verbose browser logs for ACS troubleshooting | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/how-to-collect-browser-verbose-log |
| Collect ACS call information for support diagnosis | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/how-to-collect-call-info |
| Enable and manage ACS WebJS client logging | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/how-to-collect-client-logs |
| Capture diagnostic audio recordings for ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/how-to-collect-diagnostic-audio-recordings |
| Gather Windows audio event logs for ACS issues | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/how-to-collect-windows-audio-event-log |
| Resolve cameraFreeze UFD and frozen video in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/camera-freeze |
| Interpret cameraPermissionDenied UFD in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/camera-permission-denied |
| Fix cameraStartFailed UFD when ACS video won’t start | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/camera-start-failed |
| Diagnose cameraStartTimedOut UFD in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/camera-start-timed-out |
| Handle cameraStoppedUnexpectedly UFD in ACS video | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/camera-stopped-unexpectedly |
| Fix capturerStartFailed UFD for ACS screen sharing | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/capturer-start-failed |
| Investigate capturerStoppedUnexpectedly UFD in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/capturer-stopped-unexpectedly |
| Investigate microphoneMuteUnexpectedly UFD in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/microphone-mute-unexpectedly |
| Handle microphoneNotFunctioning UFD in ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/microphone-not-functioning |
| Interpret microphonePermissionDenied UFD in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/microphone-permission-denied |
| Understand networkReceiveQuality UFD in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/network-receive-quality |
| Diagnose networkReconnect UFD and ICE failures in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/network-reconnect |
| Handle networkRelaysNotReachable UFD in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/network-relays-not-reachable |
| Understand networkSendQuality UFD in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/network-send-quality |
| Fix noMicrophoneDevicesEnumerated UFD in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/no-microphone-devices-enumerated |
| Interpret noNetwork UFD events in ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/no-network |
| Resolve noSpeakerDevicesEnumerated UFD in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/no-speaker-devices-enumerated |
| Resolve screenshareRecordingDisabled UFD on macOS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/screenshare-recording-disabled |
| Use speakingWhileMicrophoneIsMuted UFD to aid users | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/references/ufd/speaking-while-microphone-is-muted |
| Troubleshoot call end response codes across ACS SDKs | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/troubleshooting-codes |
| Avoid createView errors when disposing ACS video renderer | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/video-issues/application-disposes-video-renderer |
| Diagnose ACS createView timeout video errors | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/video-issues/create-view-timeout |
| Mitigate poor ACS video quality on bad networks | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/video-issues/network-poor |
| Recover when remote ACS video becomes unavailable | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/video-issues/remote-video-becomes-unavailable |
| Handle unavailable video subscription errors in ACS | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/video-issues/subscribing-video-not-available |
| Troubleshoot frozen sender video in ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/video-issues/video-is-frozen |
| Address high CPU impact on ACS video quality | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/video-issues/video-sender-has-high-cpu-load |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply best practices for ACS Calling SDK usage | https://learn.microsoft.com/en-us/azure/communication-services/concepts/best-practices |
| Implement answer machine detection with DTMF logic | https://learn.microsoft.com/en-us/azure/communication-services/concepts/call-automation/answer-machine-detection |
| Apply best practices for Communication Services user access tokens | https://learn.microsoft.com/en-us/azure/communication-services/concepts/credentials-best-practices |
| Manage Azure email opt-outs for B2C delivery | https://learn.microsoft.com/en-us/azure/communication-services/concepts/email/email-optout-management |
| Improve Azure email sender reputation and complaints | https://learn.microsoft.com/en-us/azure/communication-services/concepts/email/sender-reputation-managed-suppression-list |
| Govern Teams meeting experience for ACS virtual visits | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/virtual-visits/govern-meeting-experience |
| Optimize user experience for ACS–Teams virtual appointments | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/virtual-visits/plan-user-experience |
| Choose and use Raw ID string identifiers in ACS | https://learn.microsoft.com/en-us/azure/communication-services/concepts/raw-id-use-cases |
| Follow Azure SMS and email messaging policies | https://learn.microsoft.com/en-us/azure/communication-services/concepts/sms/messaging-policy |
| Fill Azure SMS short code program brief correctly | https://learn.microsoft.com/en-us/azure/communication-services/concepts/sms/program-brief-guidelines |
| Prepare 10DLC brand and campaign registration details | https://learn.microsoft.com/en-us/azure/communication-services/concepts/sms/ten-digit-long-code-guidelines |
| Complete Azure toll-free SMS verification application | https://learn.microsoft.com/en-us/azure/communication-services/concepts/sms/toll-free-verification-guidelines |
| Avoid ACS phone numbers being flagged as spam | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/prevent-spam-flag |
| Handle known Call Automation limitations and behaviors | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/known-issues-call-automation |
| Manage and improve ACS call quality in production | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/manage-call-quality |
| Apply network requirements for ACS voice and video quality | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/network-requirements |
| Apply ACS-specific UX best practices for calling | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/user-experience |
| Handle emergency calls in Teams Phone Extensibility | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/tpe/teams-phone-extensibility-emergency-call |
| Optimize ACS audio calling in Azure Virtual Desktop VDI | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/calling-from-virtual-desktop-infrastructure |
| Optimize ACS video layout and resolution on web | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/optimizing-video-placement |
| Implement a production-ready ACS authentication backend (hero sample) | https://learn.microsoft.com/en-us/azure/communication-services/samples/trusted-auth-sample |
| Prepare devices for ACS-powered virtual appointments | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/virtual-visits/extend-teams/precall |

### Decision Making
| Topic | URL |
|-------|-----|
| Use Azure Advisor recommendations for ACS optimization | https://learn.microsoft.com/en-us/azure/communication-services/concepts/advisor-overview |
| Use ACS Teams interop in government cloud environments | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/guest/government-cloud |
| Use ACS Teams user features in government cloud environments | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/teams-user/government-cloud |
| Choose PSTN connectivity options and estimate cost for Teams Phone extensibility | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/tpe/teams-phone-extensibility-connectivity-cost |
| Decide on migration from Twilio Video to ACS Calling | https://learn.microsoft.com/en-us/azure/communication-services/concepts/migrate-to-azure-communication-services |
| Choose ACS phone number types and regions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/number-types |
| Understand pricing model for ACS Teams interop scenarios | https://learn.microsoft.com/en-us/azure/communication-services/concepts/pricing/teams-interop-pricing |
| Plan ACS PSTN usage with pricing and billing rules | https://learn.microsoft.com/en-us/azure/communication-services/concepts/pstn-pricing |
| Determine Teams license requirements for ACS Teams interop | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/eligible-teams-licenses |
| Design and integrate custom event platforms with Teams and ACS | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/events-playbook |
| Migrate Twilio Video implementations to ACS Calling | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/migrating-to-azure-communication-services-calling |
| Migrate Twilio Conversations Chat to ACS Chat | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/migrating-to-azure-communication-services-chat |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Architect contact center solutions with Azure Communication Services | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/contact-center |
| Architect ACS with ExpressRoute for private connectivity | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/integrate-express-route |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Call Automation metrics definitions and units | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/call-automation-metrics |
| Supported MIME types for ACS email attachments | https://learn.microsoft.com/en-us/azure/communication-services/concepts/email/email-attachment-allowed-mime-types |
| Request higher email sending quotas in ACS | https://learn.microsoft.com/en-us/azure/communication-services/concepts/email/email-quota-increase |
| Review known issues and limitations for ACS Teams external users | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/guest/limitations |
| Argentina ACS phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-argentina |
| Australia ACS phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-australia |
| Austria ACS phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-austria |
| Belgium ACS phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-belgium |
| Brazil ACS phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-brazil |
| Canada ACS phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-canada |
| Chile ACS phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-chile |
| China ACS phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-china |
| Colombia ACS phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-colombia |
| Czech Republic ACS phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-czech-republic |
| Check Denmark phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-denmark |
| Check Estonia phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-estonia |
| Check Finland phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-finland |
| Check France phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-france |
| Check Germany phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-germany |
| Check Hong Kong phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-hong-kong |
| Check Indonesia phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-indonesia |
| Check Ireland phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-ireland |
| Check Israel phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-israel |
| Check Italy phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-italy |
| Check Japan phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-japan |
| Check Latvia phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-latvia |
| Check Lithuania phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-lithuania |
| Check Luxembourg phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-luxembourg |
| Check Malaysia phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-malaysia |
| Check Mexico phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-mexico |
| Check Netherlands phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-netherlands |
| Check New Zealand phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-new-zealand |
| Check Norway phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-norway |
| Check Philippines phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-philippines |
| Check Poland phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-poland |
| Check Portugal phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-portugal |
| Check Saudi Arabia phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-saudi-arabia |
| Check Singapore phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-singapore |
| Check Slovakia phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-slovakia |
| Check Slovenia phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-slovenia |
| Check South Africa phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-south-africa |
| Check South Korea phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-south-korea |
| Check Spain phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-spain |
| Check Sweden phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-sweden |
| Check Switzerland phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-switzerland |
| Check Taiwan phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-taiwan |
| Check Thailand phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-thailand |
| Check UAE phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-united-arab-emirates |
| Check UK phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-united-kingdom |
| Check US phone number availability and restrictions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/phone-number-management-for-united-states |
| Check country availability and eligibility for Azure numbers | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/sub-eligibility-number-capability |
| Review Azure Communication Services API limits and quotas | https://learn.microsoft.com/en-us/azure/communication-services/concepts/service-limits |
| Use certified SBCs and understand ACS direct routing limits | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/certified-session-border-controllers |
| Implement ACS emergency calling by supported regions | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/emergency-calling-concept |
| Review known telephony limitations in ACS direct routing | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/known-limitations-acs-telephony |
| Understand ACS toll-free calling limitations by region | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/toll-free-calling |
| Understand limits for ACS trial and verified phone numbers | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/trial-phone-numbers-faq |
| Review Calling SDK platform support and feature limits | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/calling-sdk-features |
| Review RAW media access constraints in ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/media-access |
| Configure Music Mode audio quality settings in ACS | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/music-mode |
| Handle ACS email sending tier limit exceptions | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email-advanced/throw-exception-when-tier-limit-reached |
| Get and manage ACS trial phone numbers with constraints | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/telephony/get-trial-phone-number |
| Resolve ACS call setup failures from invalid or expired tokens | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/call-setup-issues/invalid-or-expired-tokens |
| ACS video subscription limits on browsers | https://learn.microsoft.com/en-us/azure/communication-services/resources/troubleshooting/voice-video-calling/video-issues/reaching-max-number-of-active-video-subscriptions |

### Security
| Topic | URL |
|-------|-----|
| Understand data transfer and terms for WhatsApp in Azure | https://learn.microsoft.com/en-us/azure/communication-services/concepts/advanced-messaging/whatsapp/whatsapp-terms-of-service |
| Configure authentication methods for Azure Communication Services | https://learn.microsoft.com/en-us/azure/communication-services/concepts/authentication |
| Understand ACS call flow topologies and encryption | https://learn.microsoft.com/en-us/azure/communication-services/concepts/detailed-call-flows |
| Apply sender authentication best practices in Azure | https://learn.microsoft.com/en-us/azure/communication-services/concepts/email/email-authentication-best-practice |
| Configure Azure email domains and authentication | https://learn.microsoft.com/en-us/azure/communication-services/concepts/email/email-domain-and-sender-authentication |
| Use Azure Communication Services in US Government clouds | https://learn.microsoft.com/en-us/azure/communication-services/concepts/government |
| Configure authentication for single-tenant and multitenant ACS Teams apps | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/custom-teams-endpoint-authentication-overview |
| Configure closed captions for ACS–Teams interop calls | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/enable-closed-captions |
| Enable and license Teams interoperability for ACS users | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/enable-interoperability-teams |
| Understand security measures for ACS Teams external users | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/guest/security |
| Configure Teams admin controls for external ACS users | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/guest/teams-administration |
| Assign Microsoft Entra API permissions for ACS Teams calling | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/teams-user/azure-ad-api-permissions |
| Use Rooms API for secure structured meetings | https://learn.microsoft.com/en-us/azure/communication-services/concepts/rooms/room-concept |
| Configure ACS caller ID and CNAM registration | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/how-to-manage-your-calling-identity |
| Understand ACS closed captions behavior and data handling | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/closed-captions |
| Understand ACS Real Time Text compliance and usage | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/real-time-text |
| Secure Call Automation webhooks and Event Grid delivery | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/secure-webhook-endpoint |
| Display and consent to call transcription state in ACS | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/call-transcription |
| Use managed identity with Azure Communication Services securely | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/managed-identity |
| Set up SMTP authentication for ACS email with Entra | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email-smtp/smtp-authentication |
| Implement Azure Communication Services emergency calling | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/telephony/emergency-calling |
| Configure consent and access for Teams Phone Extensibility | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/tpe/teams-phone-extensibility-access-teams-phone |
| Sign Azure Communication Services HTTP requests with HMAC | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/hmac-header-tutorial |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Advanced Messaging diagnostic logs in Azure | https://learn.microsoft.com/en-us/azure/communication-services/concepts/advanced-messaging/logs |
| Meet prerequisites to use WhatsApp in Copilot Studio | https://learn.microsoft.com/en-us/azure/communication-services/concepts/advanced-messaging/whatsapp/whatsapp-channel-prerequisites |
| Use Azure Communication Services chat metrics in Azure Monitor | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/chat-metrics |
| Configure Azure Monitor logging and metrics for Communication Services | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/enable-logging |
| Use Call Automation Insights workbooks for monitoring | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/insights/call-automation-insights |
| Use Call Recording Insights workbooks for analytics | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/insights/call-recording-insights |
| View Azure Communication Services chat insights with Workbooks | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/insights/chat-insights |
| Use Azure Workbooks for email insights dashboards | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/insights/email-insights |
| Monitor SMS activity with Azure insights dashboard | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/insights/sms-insights |
| Use ACS voice and video insights workbooks | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/insights/voice-and-video-insights |
| Configure Call Automation logging with Azure Monitor | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/call-automation-logs |
| Use ACS call client media statistics time series logs | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/call-client-media-statistics-log-schema |
| Use ACS call client operations log schema | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/call-client-operations-log-schema |
| Understand ACS call diagnostics log schema | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/call-diagnostics-log-schema |
| Understand ACS call diagnostics updates log schema | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/call-diagnostics-updates-log-schema |
| Use ACS call metrics log schema for insights | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/call-metrics-log-schema |
| Understand ACS call summary log schema | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/call-summary-log-schema |
| Understand ACS call summary updates log schema | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/call-summary-updates-log-schema |
| Enable and interpret Azure Communication Services chat logs | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/chat-logs |
| Configure and use Azure email diagnostic logs | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/email-logs |
| Configure end of call survey logs for ACS Web SDK | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/end-of-call-survey-logs |
| Configure and interpret Call Recording summary logs | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/recording-logs |
| Enable and interpret Azure SMS diagnostic logs | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/sms-logs |
| Configure and interpret ACS voice and video call logs | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/logs/voice-and-video-logs |
| Query ACS call logs with Azure Log Analytics | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/query-call-logs |
| Query ACS call logs with Azure Log Analytics | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/query-call-logs |
| Set up monitoring and alerts for ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/set-up-call-monitoring |
| Use Azure SMS metrics and dimensions in monitoring | https://learn.microsoft.com/en-us/azure/communication-services/concepts/analytics/sms-metrics |
| Understand Azure email metric definitions and usage | https://learn.microsoft.com/en-us/azure/communication-services/concepts/email-metrics |
| Use inline attachments in ACS email messages | https://learn.microsoft.com/en-us/azure/communication-services/concepts/email/email-attachment-inline |
| Prepare ACS email resources and domains for sending | https://learn.microsoft.com/en-us/azure/communication-services/concepts/email/prepare-email-communication-resource |
| Configure firewall rules for ACS custom Teams calling apps | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/custom-teams-endpoint-firewall-configuration |
| Understand Teams user capabilities in ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/guest/calling-capabilities |
| Review capabilities for Teams external users in meetings | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/guest/meeting-capabilities |
| Understand Teams client experience for external ACS users | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/guest/teams-client-experience |
| Provision resources for Teams Phone extensibility with ACS | https://learn.microsoft.com/en-us/azure/communication-services/concepts/interop/tpe/teams-phone-extensibility-provisioning |
| Understand and use ACS metric definitions in Azure Monitor | https://learn.microsoft.com/en-us/azure/communication-services/concepts/metrics |
| Interpret Job Router metrics in Azure portal | https://learn.microsoft.com/en-us/azure/communication-services/concepts/router/metrics |
| Configure Azure SMS Opt-Out Management API | https://learn.microsoft.com/en-us/azure/communication-services/concepts/sms/opt-out-api-concept |
| Configure ACS direct routing and voice routing | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/direct-routing-provisioning |
| Configure SIP parameters for ACS direct routing | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/direct-routing-sip-specification |
| Configure inbound PSTN and direct routing endpoints in ACS | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/inbound-calling-capabilities |
| Monitor ACS direct routing components and trunks | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/monitoring-troubleshooting-telephony/monitor-direct-routing |
| Access media quality statistics via ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/media-quality-sdk |
| Configure and use ACS pre-call diagnostics API | https://learn.microsoft.com/en-us/azure/communication-services/concepts/voice-video-calling/pre-call-diagnostics |
| Validate domains for ACS direct routing SBCs | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/telephony/domain-validation |
| Enable audio-only calling mode in ACS UI Library | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/audio-only-mode |
| Configure custom button bar actions in ACS UI Library | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/button-injection |
| Enable closed captions in ACS UI Library calls | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/closed-captions |
| Inject custom user data models into ACS UI Library | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/data-model |
| Disable end-call confirmation in ACS UI Library | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/leave-call-confirmation |
| Configure localization and RTL in ACS UI Library | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/localization |
| Configure screen orientation in ACS UI Library | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/orientation |
| Set custom call titles and subtitles in ACS UI Library | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/setup-title-subtitle |
| Configure skipping setup screen in ACS UI Library | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/skip-setup-screen |
| Customize theming for ACS UI Library components | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/theming |
| Provision Azure Managed Domains for ACS email | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/add-azure-managed-domains |
| Configure custom verified email domains in ACS | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/add-custom-verified-domains |
| Manage multiple email sender addresses in ACS | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/add-multiple-senders |
| Manage ACS email sender addresses via Management SDKs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/add-multiple-senders-mgmt-sdks |
| Connect verified domains to ACS Email Communication Service | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/connect-email-communication-resource |
| Create and manage ACS Email Communication Service resources | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/create-email-communication-resource |
| Enable email engagement tracking for Azure domains | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/enable-user-engagement-tracking |
| Configure email suppression lists in Azure portal | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/manage-suppression-lists |
| Apply for Azure SMS short code provisioning | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/sms/apply-for-short-code |
| Register 10DLC brand and campaigns in Azure | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/sms/apply-for-ten-digit-long-code |
| Submit and manage Azure toll-free SMS verification | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/sms/apply-for-toll-free-verification |
| Enable alphanumeric sender ID for Azure SMS | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/sms/enable-alphanumeric-sender-id |
| Programmatically configure ACS direct routing voice rules | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/telephony/voice-routing-sdk-config |
| Configure video constraints in ACS calling apps | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-video-constraints |
| Disable local preview mirroring in ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/local-preview-mirroring |
| Migrate Android ACS push to FCM HTTP v1 | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/call-chat-migrate-android-push-fcm-v1 |
| Register ACS Android push notifications with FCM v1 | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/call-chat-register-android-push-fcm-v1 |
| Configure proxy and TURN servers for ACS calling | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/proxy-calling-support-tutorial |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Stream call audio with Call Automation Audio Streaming APIs | https://learn.microsoft.com/en-us/azure/communication-services/concepts/call-automation/audio-streaming-concept |
| Integrate Call Automation with Foundry Tools | https://learn.microsoft.com/en-us/azure/communication-services/concepts/call-automation/azure-communication-services-azure-cognitive-services-integration |
| Use Call Automation play action for audio prompts | https://learn.microsoft.com/en-us/azure/communication-services/concepts/call-automation/play-action |
| Use real-time transcription with Call Automation | https://learn.microsoft.com/en-us/azure/communication-services/concepts/call-automation/real-time-transcription |
| Gather caller input with Call Automation Recognize | https://learn.microsoft.com/en-us/azure/communication-services/concepts/call-automation/recognize-action |
| Configure push notifications for ACS chat and calling apps | https://learn.microsoft.com/en-us/azure/communication-services/concepts/notifications |
| Use ACS Number Lookup to retrieve phone insights | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/number-lookup-concept |
| Integrate ACS Number Lookup SDK into applications | https://learn.microsoft.com/en-us/azure/communication-services/concepts/numbers/number-lookup-sdk |
| Control calls with Call Automation REST actions | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/actions-for-call-control |
| Get audio streams from calls using Audio Streaming API | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/audio-streaming-quickstart |
| Use mid-call media actions with Call Automation | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/control-mid-call-media-actions |
| Pass custom context data in Call Automation calls | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/custom-context |
| Process Call Automation webhook events with event processor | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/handle-events-with-event-processor |
| Mute call participants using Call Automation APIs | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/mute-participants |
| Play audio to callers using Call Automation SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/play-action |
| Add real-time call transcription via Call Automation SDKs | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/real-time-transcription-tutorial |
| Capture DTMF input with Call Automation Recognize | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/recognize-action |
| Automatically record calls using Event Grid and Functions | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/record-every-call |
| Add Teams users to ACS calls with Call Automation | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/call-automation/teams-interop-call-automation |
| Transfer active calls between clients using ACS | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/active-call-transfer |
| Retrieve Teams audio conferencing details via ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/audio-conferencing |
| Implement Microsoft Teams breakout rooms with ACS | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/breakoutrooms |
| Check browser support using ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/browser-support |
| Pass UUI headers with ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/call-context |
| Integrate iOS CallKit with ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/callkit-integration |
| Query local user capabilities during ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/capabilities |
| Enable closed captions for ACS–Teams interop calls | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/closed-captions-teams-interop-how-to |
| Subscribe to Teams participant display name change events | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/display-name-changed |
| Render active speakers using ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/dominant-speaker |
| Subscribe to Azure Communication Services calling events | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/events |
| Detect multiple active tabs with ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/is-sdk-active-in-multiple-tabs |
| Control Teams meeting lobby with ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/lobby |
| Programmatically manage calls with ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/manage-calls |
| Track and manage Teams meeting roles via ACS SDKs | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/manage-role-assignment |
| Control video streams during ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/manage-video |
| Control participant media access in Teams via ACS | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/media-access |
| View Teams PowerPoint Live via ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/powerpoint-live |
| Enable ACS calling push notifications with Event Grid | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/push-notifications |
| Send and manage raised hand state in ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/raise-hand |
| Implement reactions in ACS and Teams calls | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/reactions |
| Enable and handle spotlight state in ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/spotlight |
| Integrate Android TelecomManager with ACS calling | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/telecommanager-integration |
| Enable Teams Together Mode using ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/together-mode |
| Transfer calls to users, numbers, or voicemail with ACS | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/calling-sdk/transfer-calls |
| Archive Azure Communication Services chat threads to custom storage | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/chat-sdk/archive-chat-threads |
| Integrate ACS chat with Teams DLP policies | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/chat-sdk/data-loss-prevention |
| Integrate Azure AI translation and sentiment with ACS chat | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/chat-sdk/translating-chats |
| Use Teams Shared Line Appearance with ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/cte-calling-sdk/shared-line-appearance |
| Accept or decline Job Router offers programmatically | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/router-sdk/accept-decline-offer |
| Use Azure Functions as Job Router rule engine | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/router-sdk/azure-function |
| Customize best-worker ranking with Azure Functions | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/router-sdk/customize-worker-scoring |
| Escalate queued jobs with Job Router SDKs | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/router-sdk/escalate-job |
| Retrieve Job Router queue wait time and position | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/router-sdk/estimated-wait-time |
| Apply Job Router classification policies via SDKs | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/router-sdk/job-classification |
| Manage Job Router queues using SDKs | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/router-sdk/manage-queue |
| Route jobs to preferred workers via Job Router | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/router-sdk/preferred-worker |
| Create scheduled jobs with Job Router SDKs | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/router-sdk/scheduled-jobs |
| Subscribe to Job Router events with Event Grid | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/router-sdk/subscribe-events |
| Integrate iOS CallKit with ACS UI Library calling | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/callkit |
| Handle Azure Communication Services UI Library events | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/events |
| Set up one-to-one calling and notifications in ACS UI Library | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/one-to-one-calling |
| Enable picture-in-picture in ACS UI Library calls | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/picture-in-picture |
| Integrate Android TelecomManager with ACS UI Library | https://learn.microsoft.com/en-us/azure/communication-services/how-tos/ui-library-sdk/telecommanager |
| Download WhatsApp media from ACS Event Grid messages | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/advanced-messaging/whatsapp/download-media |
| Integrate app with WhatsApp text and media messaging | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/advanced-messaging/whatsapp/get-started |
| Subscribe to WhatsApp Advanced Messaging events with Event Grid | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/advanced-messaging/whatsapp/handle-advanced-messaging-events |
| Implement interactive WhatsApp messages with ACS SDK | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/advanced-messaging/whatsapp/send-interactive-messages |
| Send WhatsApp reaction messages using ACS SDK | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/advanced-messaging/whatsapp/send-reaction-messages |
| Send WhatsApp sticker messages with Advanced Messages SDK | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/advanced-messaging/whatsapp/send-sticker-messages |
| Send WhatsApp template messages via Advanced Messages SDK | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/advanced-messaging/whatsapp/send-template-messages |
| Make outbound PSTN calls with Call Automation | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/call-automation/quickstart-make-an-outbound-call |
| Connect ACS chat to Microsoft Teams meetings | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/chat/meeting-interop |
| Integrate Azure OpenAI bot with ACS chat | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/chat/openai-chat-bot-integration |
| Integrate Azure Bot Service bots into ACS chat | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/chat/quickstart-botframework-integration |
| Use ACS Chat SDK in React Native apps | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/chat/react-native |
| Handle Azure email events with Event Grid | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/handle-email-events |
| Manage email suppression lists via Azure SDKs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/manage-suppression-list-management-sdks |
| Send email using ACS Email SDKs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email |
| Hydrate Azure EmailClient with existing messageId | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email-advanced/hydrate-email-client-with-message-id |
| Poll for ACS email delivery status via SDK | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email-advanced/manually-poll-for-email-status |
| Send ACS emails to multiple recipients with SDKs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email-advanced/send-email-to-multiple-recipients |
| Send ACS email with file attachments via SDKs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email-advanced/send-email-with-attachments |
| Send ACS email with inline attachments via SDKs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email-advanced/send-email-with-inline-attachments |
| Use ACS email object model to build send payloads | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email-advanced/use-email-object-model-for-payload |
| Send email to ACS via SMTP | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email-smtp/send-email-smtp |
| Send ACS email using SMTP with XOAUTH2 in .NET | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/email/send-email-smtp/send-email-smtp-oauth |
| Subscribe to Azure Communication Services events via Event Grid | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/events/subscribe-to-events |
| Create Rooms with Azure Communication Services SDKs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/rooms/get-started-rooms |
| Join a Rooms call using web or mobile SDKs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/rooms/join-rooms-call |
| Manage Rooms calls with Calling and Call Automation SDKs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/rooms/manage-rooms-call |
| Create Job Router queues, policies, workers, and jobs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/router/get-started-router |
| Integrate Azure OpenAI with Job Router worker scoring | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/router/job-router-azure-openai-integration |
| Handle Azure SMS events and delivery reports | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/sms/handle-sms-events |
| Receive and process SMS with Event Grid and Functions | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/sms/receive-sms |
| Send SMS using Azure Communication Services SDKs | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/sms/send |
| Acquire and manage phone numbers via Azure SDK/CLI | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/telephony/get-phone-number |
| Use ACS JavaScript SDK to look up phone operator info | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/telephony/number-lookup |
| Add PSTN calling to apps with ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/telephony/pstn-call |
| Handle Teams Phone Extensibility calls with Call Automation | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/tpe/teams-phone-extensibility-answer-teams-calls |
| Place outbound TPE calls using Call Automation | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/tpe/teams-phone-extensibility-server-outbound-call |
| Use Teams Phone extensibility REST API with ACS | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/tpe/teams-phone-extensiblity-rest-api |
| Integrate Adaptive Cards into ACS chat UI | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/ui-library/get-started-chat-adaptive-card |
| Integrate ACS chat UI Library composites into your app | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/ui-library/get-started-chat-ui-library |
| Integrate ACS UI Library composites into applications | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/ui-library/get-started-composites |
| Combine ACS Calling and Chat SDKs in Android apps | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-android-calling-chat-sdk |
| Use Call Recording APIs for voice and video calls | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-call-recording |
| Integrate ACS Data Channel messaging in calls | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-data-channel |
| Implement raw media access with ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-raw-media-access |
| Apply video background effects in ACS calls | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-video-effects |
| Get audio stream volume in ACS calling apps | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-volume-indicator |
| Run ACS WebJS calling in Android WebView | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-webview |
| Add closed captions to ACS calling applications | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-with-closed-captions |
| Enable Real Time Text in ACS calling apps | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-with-real-time-text |
| Add 1:1 video calling using ACS JavaScript SDK | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/get-started-with-video-calling |
| Add voice calling with ACS Calling SDK for .NET | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/getting-started-with-calling |
| Handle ACS calling events with Event Grid | https://learn.microsoft.com/en-us/azure/communication-services/quickstarts/voice-video-calling/handle-calling-events |
| Build AI virtual assistants with Call Automation and Foundry | https://learn.microsoft.com/en-us/azure/communication-services/samples/call-automation-ai |
| Integrate Call Automation with Azure OpenAI voice models | https://learn.microsoft.com/en-us/azure/communication-services/samples/call-automation-azure-openai-sample |
| Understand and customize ACS Group Chat Hero sample | https://learn.microsoft.com/en-us/azure/communication-services/samples/chat-hero-sample |
| Integrate Azure AI for presend email content checks | https://learn.microsoft.com/en-us/azure/communication-services/samples/email-detect-sensitive-content |
| Connect Microsoft Copilot Studio agents to voice calls | https://learn.microsoft.com/en-us/azure/communication-services/samples/integrate-azure-communication-services-with-copilot-studio |
| Build cross-platform ACS calling apps with UI library | https://learn.microsoft.com/en-us/azure/communication-services/samples/ui-library-cross-platform |
| Configure web push notifications for ACS calling | https://learn.microsoft.com/en-us/azure/communication-services/samples/web-calling-push-notifications-sample |
| Use ACS web calling sample code in your app | https://learn.microsoft.com/en-us/azure/communication-services/samples/web-calling-sample |
| Configure ACS chat push notifications on iOS | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/add-chat-push-notifications |
| Add AR video filters using ACS and DeepAR | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/add-video-augmented-reality-tutorial |
| Send ACS VOIP push notifications via Event Grid | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/add-voip-push-notifications-event-grid |
| Enable ACS audio noise suppression and echo removal | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/audio-quality-enhancements/add-noise-supression |
| Embed ACS Chat inside a custom Microsoft Teams app | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/chat-app-teams-embed |
| Enable file attachment interoperability in ACS chat | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/chat-interop/meeting-interop-features-file-attachment |
| Enable inline image interoperability in ACS chat | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/chat-interop/meeting-interop-features-inline-image |
| Collect user feedback with ACS UI library support form | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/collecting-user-feedback/collecting-user-feedback |
| Implement ACS End of Call Survey in applications | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/end-of-call-survey-tutorial |
| Implement ACS chat file sharing via Blob Storage | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/file-sharing-tutorial-acs-chat |
| Enable file sharing in ACS–Teams interop chat | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/file-sharing-tutorial-interop-chat |
| Configure inline images for ACS–Teams interop chat | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/inline-image-tutorial-interop-chat |
| Retrieve ACS Calling SDK log files from devices | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/log-file-retrieval-tutorial |
| Integrate Azure URL Shortener with SMS messaging | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/sms-url-shortener |
| Build a trusted authentication service for ACS with Azure Functions | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/trusted-service-tutorial |
| Automate pre/post Teams appointments with Power Automate | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/virtual-visits/extend-teams/before-and-after-appointment |
| Extend Teams virtual appointment calls with ACS | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/virtual-visits/extend-teams/call |
| Integrate custom scheduling with Teams virtual appointments | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/virtual-visits/extend-teams/schedule |
| Attach custom telemetry tags in ACS Calling SDK | https://learn.microsoft.com/en-us/azure/communication-services/tutorials/voice-video-calling/diagnostic-options-tag |

### Deployment
| Topic | URL |
|-------|-----|
| Meet infrastructure requirements for ACS direct routing | https://learn.microsoft.com/en-us/azure/communication-services/concepts/telephony/direct-routing-infrastructure |
| Automate ACS and Email resource deployment with PowerShell | https://learn.microsoft.com/en-us/azure/communication-services/samples/email-resource-management |