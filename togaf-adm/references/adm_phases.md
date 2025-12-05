# Documentación Detallada de las Fases del ADM de TOGAF

## Tabla de Contenidos
1. [Fase Preliminar](#fase-preliminar)
2. [Fase A - Visión de Arquitectura](#fase-a---visión-de-arquitectura)
3. [Fase B - Arquitectura de Negocio](#fase-b---arquitectura-de-negocio)
4. [Fase C - Arquitecturas de Sistemas de Información](#fase-c---arquitecturas-de-sistemas-de-información)
5. [Fase D - Arquitectura Tecnológica](#fase-d---arquitectura-tecnológica)
6. [Fase E - Oportunidades y Soluciones](#fase-e---oportunidades-y-soluciones)
7. [Fase F - Planificación de la Migración](#fase-f---planificación-de-la-migración)
8. [Fase G - Gobernanza de la Implementación](#fase-g---gobernanza-de-la-implementación)
9. [Fase H - Gestión del Cambio de Arquitectura](#fase-h---gestión-del-cambio-de-arquitectura)
10. [Gestión de Requerimientos](#gestión-de-requerimientos)

---

## Fase Preliminar

### Objetivo
Preparar la organización para proyectos exitosos de arquitectura empresarial estableciendo el marco, principios y gobierno.

### Actividades Clave
1. **Definir el marco de arquitectura empresarial**
   - Adaptar TOGAF a las necesidades de la organización
   - Definir método, procesos y herramientas

2. **Establecer principios de arquitectura**
   - Definir principios de negocio, datos, aplicaciones y tecnología
   - Documentar rationale y consecuencias de cada principio

3. **Identificar stakeholders clave**
   - Mapear stakeholders por interés e influencia
   - Definir mecanismos de comunicación

4. **Definir modelo de gobierno**
   - Establecer comités de arquitectura
   - Definir procesos de aprobación y escalamiento
   - Establecer compliance y KPIs

### Artefactos Principales
- **Catálogo de Principios de Arquitectura**: Lista de principios guía
- **Catálogo de Stakeholders**: Identificación de partes interesadas
- **Modelo de Gobierno**: Estructura de toma de decisiones
- **Framework de Arquitectura Adaptado**: TOGAF customizado

### Ejemplo - Startup Fintech
```
Principios clave:
- P1: Seguridad primero - Todos los datos financieros deben estar encriptados en reposo y tránsito
- P2: Escalabilidad cloud-native - Priorizar soluciones serverless y auto-escalables
- P3: Compliance regulatorio - Cumplir PCI-DSS, GDPR desde el diseño
- P4: API-first - Toda funcionalidad debe exponerse mediante APIs
- P5: Time-to-market - Priorizar build vs buy en favor de soluciones SaaS probadas

Stakeholders:
- CEO/Founders: Visión y estrategia
- CTO: Decisiones técnicas
- CISO: Seguridad y compliance
- CFO: Presupuesto y ROI
- Reguladores: Cumplimiento normativo
```

---

## Fase A - Visión de Arquitectura

### Objetivo
Crear una visión de alto nivel del cambio que se va a implementar, obteniendo aprobación de stakeholders.

### Actividades Clave
1. **Establecer el proyecto de arquitectura**
   - Definir alcance (corporativo, dominio, proyecto)
   - Identificar restricciones (tiempo, presupuesto, tecnología)
   - Definir horizonte temporal

2. **Identificar drivers de negocio**
   - Objetivos estratégicos
   - Capacidades de negocio requeridas
   - KPIs y métricas de éxito

3. **Definir arquitectura baseline (AS-IS)**
   - Documentar estado actual de forma ligera
   - Identificar pain points principales

4. **Crear arquitectura objetivo (TO-BE)**
   - Visión de alto nivel del estado futuro
   - Casos de uso clave
   - Beneficios esperados

5. **Análisis de brechas preliminar**
   - Identificar diferencias principales entre AS-IS y TO-BE
   - Estimar impacto y esfuerzo

### Artefactos Principales
- **Documento de Visión de Arquitectura**: Narrativa del cambio
- **Statement of Architecture Work**: Definición del proyecto
- **Catálogo de Capacidades de Negocio**: Capacidades actuales y requeridas
- **Matriz de Stakeholders vs Capacidades**: Impacto en stakeholders
- **Análisis de Brechas**: Diferencias AS-IS vs TO-BE

### Ejemplo - Migración a Cloud
```
Visión:
"Migrar infraestructura on-premise a AWS para mejorar escalabilidad,
reducir costos operativos en 30% y habilitar expansión internacional"

Drivers de Negocio:
- D1: Expansión a 5 nuevos países en 18 meses
- D2: Reducir CAPEX de infraestructura
- D3: Mejorar disponibilidad (objetivo: 99.9%)
- D4: Acelerar time-to-market de nuevas features

Casos de Uso Clave:
- CU1: Desplegar instancias en nuevas regiones en <24h
- CU2: Auto-escalar ante picos de tráfico
- CU3: Disaster recovery automático

Arquitectura Baseline:
- 3 datacenters on-premise propios
- Servidores físicos con capacidad fija
- Backup manual diario
- Despliegues manuales 1 vez por semana

Arquitectura Objetivo:
- Multi-region AWS (us-east-1, eu-west-1, ap-southeast-1)
- ECS/EKS para contenedores auto-escalables
- RDS Multi-AZ para bases de datos
- S3 + CloudFront para estáticos
- CI/CD automatizado (múltiples deploys diarios)

Brechas Principales:
- BP1: Aplicaciones monolíticas no preparadas para cloud
- BP2: Falta expertise en AWS en el equipo
- BP3: Procesos de seguridad on-premise no aplicables
- BP4: Modelo de costos CAPEX → OPEX requiere cambio cultural
```

---

## Fase B - Arquitectura de Negocio

### Objetivo
Desarrollar la arquitectura de negocio objetivo que soporte la visión, identificando capacidades, procesos, roles y estructura organizacional.

### Actividades Clave
1. **Modelar capacidades de negocio**
   - Identificar capacidades actuales y requeridas
   - Clasificar por nivel de madurez
   - Priorizar capacidades críticas

2. **Mapear procesos de negocio**
   - Identificar procesos clave (alto nivel)
   - Modelar flujos principales
   - Identificar puntos de integración

3. **Definir roles y actores**
   - Mapear roles de negocio
   - Identificar responsabilidades (RACI)

4. **Análisis de brechas de negocio**
   - Comparar capacidades/procesos AS-IS vs TO-BE
   - Identificar nuevas capacidades necesarias

### Artefactos Principales
- **Catálogo de Capacidades de Negocio**: Lista detallada de capacidades
- **Mapa de Capacidades**: Visualización jerárquica
- **Catálogo de Procesos de Negocio**: Procesos principales
- **Diagrama de Procesos**: Flujos clave (alto nivel)
- **Catálogo de Roles**: Roles y responsabilidades
- **Matriz Proceso-Rol**: Quién hace qué
- **Análisis de Brechas de Negocio**: Cambios necesarios

### Ejemplo - Startup Fintech
```
Capacidades de Negocio Clave:

Nivel 1:
- Originación de Créditos
- Análisis de Riesgo
- Procesamiento de Pagos
- Gestión de Clientes
- Cumplimiento Regulatorio

Nivel 2 (bajo Originación de Créditos):
- Onboarding Digital
- Verificación de Identidad
- Análisis Crediticio
- Aprobación Automática
- Firma Electrónica
- Desembolso

Procesos Clave:
1. Solicitud de Crédito (end-to-end)
   - Cliente envía solicitud → Verificación KYC → Scoring automático
   → Aprobación/Rechazo → Firma → Desembolso

2. Procesamiento de Pagos
   - Cliente paga → Validación → Actualización saldo → Notificación

3. Gestión de Morosidad
   - Detección → Notificación automática → Reestructuración → Cobranza

Roles:
- Cliente: Solicita y paga créditos
- Analista de Riesgo: Revisa casos complejos
- Oficial de Compliance: Supervisa cumplimiento regulatorio
- Sistema: Procesamiento automático (90% de casos)

Brechas:
- BG1: Falta capacidad de "Originación Omnicanal" (actualmente solo web)
- BG2: Proceso de scoring es manual (necesita automatización con ML)
- BG3: No existe capacidad de "Detección de Fraude en Tiempo Real"
```

---

## Fase C - Arquitecturas de Sistemas de Información

### Objetivo
Desarrollar las arquitecturas de datos y aplicaciones que soporten la arquitectura de negocio.

### Actividades Clave

**C.1 - Arquitectura de Datos:**
1. Identificar entidades de datos críticas
2. Definir modelo de datos lógico
3. Establecer flujos de datos principales
4. Definir estrategia de datos maestros
5. Análisis de brechas de datos

**C.2 - Arquitectura de Aplicaciones:**
1. Identificar aplicaciones actuales y requeridas
2. Definir componentes de aplicación
3. Establecer interfaces y servicios
4. Mapear aplicaciones a capacidades de negocio
5. Análisis de brechas de aplicaciones

### Artefactos Principales

**Datos:**
- **Catálogo de Entidades de Datos**: Lista de entidades críticas
- **Modelo de Datos Lógico**: Entidades y relaciones
- **Diagrama de Flujo de Datos**: Movimiento de datos
- **Matriz Dato-Aplicación**: Qué aplicación gestiona qué dato

**Aplicaciones:**
- **Catálogo de Aplicaciones**: Inventario de sistemas
- **Diagrama de Componentes**: Arquitectura lógica
- **Matriz Aplicación-Capacidad**: Qué aplicación soporta qué capacidad
- **Matriz Aplicación-Proceso**: Qué aplicación soporta qué proceso
- **Análisis de Brechas de Aplicaciones**: Cambios necesarios

### Ejemplo - Startup Fintech

**Arquitectura de Datos:**
```
Entidades Críticas:
- Cliente (PII encriptado)
- Solicitud de Crédito
- Score Crediticio (con trazabilidad de versión)
- Transacción
- Cuenta
- Regla de Negocio (versionada)
- Evento de Auditoría

Flujos de Datos Clave:
1. Cliente → KYC Provider → Sistema Core
2. Sistema Core → Bureau de Crédito → Score Engine
3. Score Engine → Reglas de Negocio → Decisión
4. Sistema Core → Payment Gateway → Bank
5. Todas las operaciones → Data Lake (Analytics)

Estrategia de Datos:
- Master Data: Clientes en PostgreSQL (encriptado)
- Transaccional: PostgreSQL (ACID)
- Analytics: Snowflake (replicación asíncrona)
- Cache: Redis (sesiones, scoring temporal)
- Documentos: S3 (contratos firmados, KYC docs)
```

**Arquitectura de Aplicaciones:**
```
Aplicaciones Core (TO-BE):

1. Customer Portal (React SPA)
   - Soporta: Onboarding, Solicitud, Consulta
   - Integra con: API Gateway

2. Lending Core API (Node.js microservices)
   - Gestiona: Solicitudes, Cuentas, Transacciones
   - Expone: REST/GraphQL API
   - Integra con: Score Engine, Payment Service

3. Score Engine (Python ML service)
   - Procesa: Modelos de scoring
   - Integra con: Bureau APIs, Data Lake
   - Patrón: Event-driven (Kafka)

4. Payment Service (Java/Spring Boot)
   - Gestiona: Pagos, Desembolsos
   - Integra con: Stripe, PayPal, Banks
   - Patrón: Transaccional + Circuit Breaker

5. Compliance & Audit Service (Go)
   - Gestiona: Reglas regulatorias, Auditoría
   - Patrón: Event Sourcing

6. Notification Service (Node.js)
   - Gestiona: Email, SMS, Push
   - Integra con: SendGrid, Twilio, Firebase

7. Analytics Platform (dbt + Snowflake)
   - Procesa: BI, Reportes regulatorios
   - Integra con: Data Lake

Matriz Aplicación-Capacidad:
| Capacidad              | Customer Portal | Lending Core | Score Engine | Payment Service |
|------------------------|----------------|--------------|--------------|-----------------|
| Onboarding Digital     | ✓              | ✓            |              |                 |
| Análisis Crediticio    |                | ✓            | ✓            |                 |
| Aprobación Automática  |                | ✓            | ✓            |                 |
| Desembolso             |                | ✓            |              | ✓               |
| Procesamiento de Pagos |                | ✓            |              | ✓               |

Brechas de Aplicaciones:
- BA1: Sistema actual es monolito PHP (migrar a microservicios)
- BA2: No existe Score Engine (actualmente scoring manual en Excel)
- BA3: Payment Service actual no soporta múltiples providers
- BA4: No existe servicio de detección de fraude en tiempo real
```

---

## Fase D - Arquitectura Tecnológica

### Objetivo
Desarrollar la arquitectura tecnológica que soporte las arquitecturas de aplicaciones y datos.

### Actividades Clave
1. **Identificar plataformas tecnológicas**
   - Infraestructura (cloud, on-premise, híbrido)
   - Plataformas de desarrollo
   - Middleware y servicios compartidos

2. **Definir patrones de integración**
   - APIs, mensajería, eventos
   - Seguridad y autenticación
   - Resiliencia y manejo de errores

3. **Establecer arquitectura de referencia**
   - Capas lógicas
   - Componentes técnicos estándar
   - Patrones de diseño recomendados

4. **Análisis de brechas tecnológicas**
   - Comparar stack actual vs requerido
   - Identificar migraciones necesarias

### Artefactos Principales
- **Catálogo de Tecnologías**: Inventario de plataformas y herramientas
- **Diagrama de Arquitectura Tecnológica**: Vista de infraestructura
- **Matriz Aplicación-Tecnología**: Qué tecnología usa cada aplicación
- **Documento de Estándares Técnicos**: Patrones y mejores prácticas
- **Análisis de Brechas Tecnológicas**: Cambios necesarios

### Ejemplo - Migración a Cloud

```
Stack Tecnológico Target (AWS):

**Compute:**
- Frontend: S3 + CloudFront + Route53
- Backend APIs: ECS Fargate (contenedores serverless)
- ML/Batch: Lambda + Step Functions
- Alternativa: EKS si se necesita Kubernetes

**Data:**
- Relacional: RDS PostgreSQL Multi-AZ (escritura) + Read Replicas
- Cache: ElastiCache Redis (cluster mode)
- Búsqueda: OpenSearch (para logs y analytics)
- Data Lake: S3 + Glue + Athena
- DWH: Redshift o Snowflake (evaluar)
- Streaming: MSK (Managed Kafka)

**Integration:**
- API Gateway: AWS API Gateway + ALB
- Autenticación: Cognito + OAuth2/OIDC
- Service Mesh: AWS App Mesh (si se usa EKS)
- Mensajería async: SQS/SNS
- Eventos: EventBridge

**DevOps:**
- CI/CD: GitHub Actions + AWS CodeDeploy
- IaC: Terraform
- Monitoring: CloudWatch + Grafana + Datadog
- Logging: CloudWatch Logs → OpenSearch
- Tracing: X-Ray
- Secrets: AWS Secrets Manager

**Security:**
- Network: VPC, Security Groups, NACLs
- Firewall: WAF + Shield (DDoS protection)
- Encryption: KMS para datos en reposo
- Identity: IAM + SSO
- Compliance: Config + Security Hub + GuardDuty
- Pentest: Automated scans con Prowler

**Backup & DR:**
- RDS automated backups (7 días)
- S3 versioning + Lifecycle policies
- Multi-region replication para DR
- RTO: 4 horas, RPO: 15 minutos

Patrones de Integración:

1. **API Gateway Pattern:**
   - Cliente → API Gateway → ALB → ECS Services
   - Rate limiting, throttling, API keys
   - Request/response transformation

2. **Event-Driven Pattern:**
   - Service A → EventBridge → Lambda → Service B
   - Desacoplamiento asíncrono
   - Retry automático

3. **CQRS Pattern:**
   - Write: PostgreSQL (transaccional)
   - Read: ElastiCache (cache) + Read Replicas
   - Sync: Change Data Capture (CDC)

4. **Circuit Breaker Pattern:**
   - Para integraciones externas (Stripe, KYC providers)
   - Implementado en app layer o con service mesh

5. **Saga Pattern:**
   - Para transacciones distribuidas (ej: desembolso)
   - Orchestration con Step Functions

Matriz Aplicación-Tecnología:
| Aplicación           | Compute    | Database   | Cache | Integration      |
|----------------------|------------|------------|-------|------------------|
| Customer Portal      | S3+CF      | -          | -     | API Gateway      |
| Lending Core API     | ECS        | RDS PG     | Redis | ALB+EventBridge  |
| Score Engine         | Lambda+ECS | RDS Read   | Redis | MSK+EventBridge  |
| Payment Service      | ECS        | RDS PG     | Redis | ALB+SQS          |
| Notification Service | Lambda     | DynamoDB   | -     | SNS+SQS          |
| Analytics Platform   | Glue+Athena| S3+Redshift| -     | S3 Events        |

Brechas Tecnológicas:
- BT1: Migrar de VMs on-premise a contenedores ECS
- BT2: Migrar de Oracle a PostgreSQL RDS
- BT3: Implementar API Gateway (actualmente acceso directo)
- BT4: Implementar observabilidad completa (actualmente logs básicos)
- BT5: Implementar IaC (actualmente infraestructura manual)
- BT6: Capacitar equipo en AWS, contenedores y IaC
```

---

## Fase E - Oportunidades y Soluciones

### Objetivo
Consolidar los análisis de brechas en un conjunto de paquetes de trabajo priorizados y agrupados que puedan implementarse.

### Actividades Clave
1. **Revisar brechas consolidadas**
   - Integrar brechas de Negocio, Datos, Aplicaciones y Tecnología
   - Identificar dependencias entre cambios

2. **Agrupar cambios en paquetes de trabajo**
   - Definir proyectos o releases
   - Agrupar por valor de negocio y dependencias

3. **Evaluar opciones de implementación**
   - Build vs Buy
   - Migración Big Bang vs Incremental
   - Opciones tecnológicas

4. **Priorizar iniciativas**
   - Valor de negocio vs esfuerzo
   - Quick wins vs transformación profunda
   - Gestión de riesgos

### Artefactos Principales
- **Análisis Consolidado de Brechas**: Todas las brechas integradas
- **Catálogo de Paquetes de Trabajo**: Proyectos/releases definidos
- **Matriz de Dependencias**: Relaciones entre paquetes
- **Análisis de Beneficios**: Valor esperado por iniciativa
- **Evaluación de Riesgos**: Riesgos por paquete y mitigaciones

### Ejemplo - Migración a Cloud

```
Análisis Consolidado de Brechas (priorizadas):

| ID  | Brecha                                  | Tipo  | Impacto | Esfuerzo | Prioridad |
|-----|-----------------------------------------|-------|---------|----------|-----------|
| BP1 | Aplicaciones monolíticas                | App   | Alto    | Alto     | CRÍTICO   |
| BT1 | Migrar VMs a contenedores               | Tech  | Alto    | Alto     | CRÍTICO   |
| BT2 | Migrar Oracle a PostgreSQL              | Tech  | Alto    | Alto     | CRÍTICO   |
| BA2 | Implementar Score Engine automatizado   | App   | Alto    | Medio    | ALTO      |
| BT3 | Implementar API Gateway                 | Tech  | Medio   | Bajo     | ALTO      |
| BG3 | Detección de fraude en tiempo real      | Neg   | Alto    | Alto     | MEDIO     |
| BT4 | Observabilidad completa                 | Tech  | Medio   | Medio    | MEDIO     |
| BT5 | Implementar IaC                         | Tech  | Medio   | Medio    | MEDIO     |
| BA3 | Payment Service multi-provider          | App   | Bajo    | Bajo     | BAJO      |

Paquetes de Trabajo Propuestos:

**Release 1: Fundación Cloud (Meses 1-3)**
- Objetivo: Establecer base AWS y migrar primer workload
- Alcance:
  - Setup cuenta AWS (organizaciones, redes, seguridad baseline)
  - Implementar IaC con Terraform
  - Implementar CI/CD pipeline
  - Migrar aplicación read-only (Analytics) como piloto
  - Setup observabilidad básica (logs, métricas)
- Valor: Validar patrón de migración, reducir riesgo
- Esfuerzo: 3 personas-mes
- Riesgo: BAJO (no afecta sistemas críticos)

**Release 2: Plataforma Core (Meses 4-7)**
- Objetivo: Migrar aplicaciones transaccionales críticas
- Alcance:
  - Migrar base de datos Oracle → RDS PostgreSQL
  - Refactorizar monolito PHP → microservicios (Lending Core API)
  - Implementar API Gateway + autenticación
  - Migrar Customer Portal a S3+CloudFront
  - Implementar cache Redis
- Dependencias: Release 1 completado
- Valor: 30% reducción de costos operativos, mejora performance
- Esfuerzo: 8 personas-mes
- Riesgo: ALTO (afecta operación core)
  - Mitigación: Blue-green deployment, rollback plan, periodo de coexistencia

**Release 3: Capacidades Avanzadas (Meses 8-10)**
- Objetivo: Habilitar nuevas capacidades de negocio
- Alcance:
  - Implementar Score Engine con ML
  - Implementar Payment Service multi-provider
  - Implementar detección de fraude básica
  - Multi-region setup (us-east + eu-west)
- Dependencias: Release 2 completado
- Valor: Reducir tasa de rechazo en 15%, habilitar expansión internacional
- Esfuerzo: 6 personas-mes
- Riesgo: MEDIO

**Release 4: Optimización (Meses 11-12)**
- Objetivo: Optimizar operación y observabilidad
- Alcance:
  - Observabilidad avanzada (tracing distribuido)
  - Auto-scaling optimizado
  - Detección de fraude en tiempo real
  - Disaster Recovery automatizado
  - Cost optimization
- Dependencias: Release 3 completado
- Valor: Mejora operacional, reducción incidentes en 40%
- Esfuerzo: 4 personas-mes
- Riesgo: BAJO

Matriz de Dependencias:
Release 1 → Release 2 → Release 3 → Release 4
           (CRÍTICO)   (SECUENCIAL) (SECUENCIAL)

Decisiones Build vs Buy:
- Lending Core: BUILD (diferenciador competitivo)
- Score Engine: BUILD (ventaja competitiva en ML)
- Payment Service: BUILD wrapper + BUY providers (Stripe, PayPal)
- Notification Service: BUY (SendGrid, Twilio) + wrapper ligero
- Observabilidad: BUY (Datadog/New Relic)
- IaC/DevOps: BUILD sobre herramientas open source (Terraform, GitHub Actions)

Riesgos Principales:
- R1: Downtime durante migración DB → Mitigación: Blue-green, ventana de mantenimiento
- R2: Falta expertise AWS en equipo → Mitigación: Contratar 2 cloud engineers, training
- R3: Sobrecoste cloud → Mitigación: FinOps desde día 1, reserved instances
- R4: Problemas de performance post-migración → Mitigación: Load testing extensivo, rollback plan
```

---

## Fase F - Planificación de la Migración

### Objetivo
Crear una hoja de ruta detallada con cronograma, recursos, costos y plan de implementación.

### Actividades Clave
1. **Secuenciar paquetes de trabajo**
   - Definir orden de implementación
   - Identificar dependencias críticas
   - Establecer hitos principales

2. **Estimar recursos y costos**
   - Equipo necesario por fase
   - Costos de implementación
   - Costos de operación (run rate)

3. **Definir criterios de transición**
   - Go/no-go criteria
   - Definition of Done por release
   - Estrategia de cutover

4. **Gestionar riesgos**
   - Plan de contingencia
   - Rollback procedures
   - Communication plan

### Artefactos Principales
- **Roadmap de Implementación**: Cronograma visual con hitos
- **Plan de Migración Detallado**: Secuencia de actividades por release
- **Matriz de Transición**: Estado AS-IS → TO-BE por componente
- **Plan de Recursos**: Staffing por fase
- **Presupuesto**: Costos estimados por fase
- **Registro de Riesgos**: Riesgos, impacto, probabilidad, mitigaciones

### Ejemplo - Migración a Cloud

```
Roadmap de Alto Nivel (12 meses):

Q1: Fundación
├─ Mes 1: Setup AWS + IaC
├─ Mes 2: CI/CD + Piloto Analytics
└─ Mes 3: Validación y lecciones aprendidas

Q2-Q3: Core Migration
├─ Mes 4: DB Migration preparation (Oracle→PostgreSQL)
├─ Mes 5: Refactoring monolito → microservicios
├─ Mes 6: Migración frontend + API Gateway
└─ Mes 7: Go-live core + estabilización

Q3-Q4: Capacidades Avanzadas
├─ Mes 8: Score Engine ML
├─ Mes 9: Payment Service + Multi-region
└─ Mes 10: Fraud detection

Q4: Optimización
├─ Mes 11: Observabilidad avanzada + DR
└─ Mes 12: Optimización y cierre

Hitos Clave:
- ✓ Milestone 1 (Fin Mes 3): Primer workload en AWS funcionando
- ✓ Milestone 2 (Fin Mes 7): Core transaccional 100% en AWS, on-premise apagado
- ✓ Milestone 3 (Fin Mes 10): Capacidades nuevas en producción
- ✓ Milestone 4 (Fin Mes 12): Proyecto cerrado, operación normal

Plan de Migración Detallado - Release 2 (Core):

Semana 1-2: Preparación
- Freeze de cambios en monolito (code freeze)
- Backup completo + validación
- Setup entorno PostgreSQL en RDS
- Setup ECS cluster + networking

Semana 3-4: Migración de Datos
- Migración inicial Oracle → PostgreSQL (bulk)
- Validación de integridad de datos
- Setup replicación continua (GoldenGate o AWS DMS)
- Testing de queries en PostgreSQL

Semana 5-8: Despliegue de Microservicios
- Deploy Lending Core API en ECS (blue environment)
- Deploy Customer Portal en S3+CloudFront
- Deploy API Gateway
- Testing integrado (sin tráfico real)

Semana 9: Transición
- Cutover plan:
  - Viernes 10pm: Apagar monolito PHP
  - Migración final incremental de datos (últimas horas)
  - Validación final de datos
  - Sábado 2am: Switch DNS a nueva infraestructura
  - Sábado 2am-6am: Smoke testing
  - Sábado 6am: Go/no-go decision
  - Sábado 8am: Apertura de servicio
- Rollback plan si falla:
  - Revertir DNS a on-premise
  - Re-sincronizar datos desde backup
  - RTO: 2 horas

Semana 10-12: Estabilización
- Monitoreo 24/7
- Bug fixing
- Performance tuning
- Apagado definitivo on-premise (semana 12)

Matriz de Transición:

| Componente        | AS-IS           | Estado Intermedio | TO-BE           | Fecha Target |
|-------------------|-----------------|-------------------|-----------------|--------------|
| Database          | Oracle on-prem  | Replicación dual  | RDS PostgreSQL  | Mes 7        |
| App Backend       | Monolito PHP    | Coexistencia      | ECS microservs  | Mes 7        |
| App Frontend      | Apache on-prem  | -                 | S3+CloudFront   | Mes 6        |
| API Gateway       | No existe       | -                 | AWS API Gateway | Mes 6        |
| Cache             | Memcached local | -                 | ElastiCache     | Mes 7        |
| Files/Docs        | NFS on-prem     | S3+sync           | S3              | Mes 6        |

Plan de Recursos:

Roles necesarios:
- 1 Solution Architect (12 meses, 100%)
- 2 Cloud Engineers/DevOps (12 meses, 100%)
- 3 Backend Developers (meses 4-10, 100%)
- 1 Frontend Developer (meses 5-7, 100%)
- 1 DBA (meses 4-8, 100%)
- 1 QA Engineer (meses 6-10, 50%)
- 1 Security Engineer (meses 1-12, 25%)

Total: ~8.5 FTE promedio

Presupuesto Estimado:

CAPEX (One-time):
- Staffing (8.5 FTE x 12 meses x $10k/mes): $1,020k
- Consultoría AWS (opcional): $100k
- Herramientas/Licencias (Terraform Enterprise, etc.): $50k
- Capacitación del equipo: $30k
- Contingencia (15%): $180k
Total CAPEX: $1,380k

OPEX (Recurrente - run rate mensual):
- AWS Compute (ECS): $8k/mes
- AWS Database (RDS): $5k/mes
- AWS Storage (S3+EBS): $2k/mes
- AWS Networking (bandwidth): $3k/mes
- AWS Otros (CloudFront, API Gateway, etc.): $2k/mes
- Monitoreo (Datadog): $2k/mes
- Otros SaaS: $1k/mes
Total OPEX: $23k/mes ($276k/año)

Comparación:
- OPEX actual on-premise: $40k/mes ($480k/año)
- Ahorro anual: $204k (43% reducción)
- Payback period: ~7 meses

Riesgos y Mitigaciones:

| Riesgo                          | Prob. | Impacto | Mitigación                                    |
|---------------------------------|-------|---------|-----------------------------------------------|
| Downtime prolongado en cutover  | Media | Alto    | Blue-green deploy, rollback plan, ventana 8h  |
| Pérdida de datos en migración   | Baja  | Crítico | Backups múltiples, validación checksums, DR   |
| Performance degradation         | Media | Alto    | Load testing previo, auto-scaling, monitoring |
| Sobrecosto AWS                  | Alta  | Medio   | FinOps desde día 1, alertas de billing        |
| Equipo sin expertise AWS        | Alta  | Medio   | Contratar 2 cloud engineers, training         |
| Vendor lock-in AWS              | Baja  | Medio   | Usar abstracciones, Terraform, evitar AWS-only|
| Falla de servicios AWS          | Baja  | Alto    | Multi-AZ, multi-region DR, monitoring         |
| Resistencia al cambio del equipo| Media | Medio   | Change management, comunicación, training     |

Criterios de Go/No-Go (por release):

Release 2 - Migración Core:
- ✓ Todos los tests de integración pasan (>99% success rate)
- ✓ Performance testing cumple SLAs (p95 latency <500ms)
- ✓ Security scan sin vulnerabilidades críticas
- ✓ Data integrity validation 100% exitosa
- ✓ Rollback plan probado exitosamente
- ✓ Equipo de on-call capacitado y disponible 24/7
- ✓ Stakeholders de negocio aprueban go-live
- ✓ Plan de comunicación a clientes ejecutado
```

---

## Fase G - Gobernanza de la Implementación

### Objetivo
Proveer supervisión arquitectural durante la implementación, asegurando que la solución implementada está alineada con la arquitectura definida.

### Actividades Clave
1. **Establecer estructura de gobernanza**
   - Definir comités de revisión (Architecture Review Board)
   - Establecer checkpoints de revisión
   - Definir procesos de escalamiento

2. **Realizar revisiones de arquitectura**
   - Revisiones de diseño detallado
   - Revisiones de código/infraestructura
   - Validación de compliance

3. **Gestionar cambios y desviaciones**
   - Proceso de solicitud de cambio arquitectural
   - Evaluación de impacto
   - Aprobación/rechazo y tracking

4. **Monitorear conformidad**
   - Verificar cumplimiento de principios
   - Validar uso de patrones estándar
   - Medir KPIs arquitecturales

### Artefactos Principales
- **Contrato de Arquitectura**: Acuerdo entre arquitectos y equipos de implementación
- **Reporte de Conformidad**: Estado de cumplimiento por proyecto
- **Registro de Desviaciones**: Cambios aprobados vs arquitectura original
- **Reporte de Revisión de Arquitectura**: Resultado de cada revisión formal

### Ejemplo - Startup Fintech

```
Estructura de Gobernanza:

Architecture Review Board (ARB):
- CTO (chair)
- Lead Architect
- Tech Leads por dominio (Backend, Frontend, Data, Infra)
- Security Lead
- Product Manager (voice, no vote)

Frecuencia de reuniones:
- ARB quincenal (revisión de decisiones mayores)
- Design reviews ad-hoc (según necesidad de cada equipo)
- Retrospectiva mensual de arquitectura

Proceso de Revisión:

**Nivel 1 - Design Review (ligero, <1h):**
Trigger: Antes de comenzar desarrollo de nueva feature/servicio
Asistentes: Lead Architect + Tech Lead del equipo
Alcance: Revisar diseño técnico, validar patrones, identificar riesgos
Output: Aprobado / Aprobado con cambios / Escalado a ARB

**Nivel 2 - ARB Review (formal, 2h):**
Trigger:
- Nuevos servicios/componentes
- Cambios en integraciones críticas
- Cambios en stack tecnológico
- Desviaciones de estándares
- Decisiones con impacto >$50k o >2 meses de esfuerzo

Template de solicitud:
1. Contexto y problema a resolver
2. Opciones evaluadas (con pros/cons)
3. Opción recomendada y rationale
4. Impacto en arquitectura actual
5. Riesgos y mitigaciones
6. Estimación de esfuerzo y costo

Output: Aprobado / Rechazado / Aprobado con condiciones

**Nivel 3 - Code/IaC Review (continuo):**
- Todos los PRs revisados por al menos 1 Tech Lead
- Security review automático (SonarQube, Checkov)
- Architecture review en PRs que tocan componentes core (label "arch-review")

Criterios de Conformidad:

**Principios (must-have):**
- ✓ P1: Seguridad primero - Zero defectos críticos en security scan
- ✓ P2: Escalabilidad cloud-native - Todos los servicios stateless, auto-scaling configurado
- ✓ P3: Compliance regulatorio - PCI-DSS/GDPR checklist completada
- ✓ P4: API-first - OpenAPI spec publicada antes de implementar
- ✓ P5: Time-to-market - Preferencia por SaaS validado vs build custom

**Patrones estándar (should-have):**
- REST APIs con versionado (/v1/, /v2/)
- Autenticación OAuth2 + JWT
- Logging estructurado (JSON) con trace IDs
- Métricas en Prometheus format
- Circuit breaker en integraciones externas
- IaC con Terraform (no ClickOps)
- CI/CD con tests automatizados (>80% coverage)

**Métricas de conformidad:**
- % de servicios con health checks: Target 100%
- % de APIs con rate limiting: Target 100%
- % de infraestructura como código: Target 100%
- % de servicios con SLO definido: Target 100%
- % de PRs con security scan passed: Target 100%
- Test coverage promedio: Target >80%

Ejemplo de Desviación Aprobada:

**Solicitud:** Usar MongoDB en vez de PostgreSQL para servicio de Notificaciones
**Rationale:**
- Volumetría muy alta (>1M docs/día)
- Modelo de datos flexible (schemas variables de notificaciones)
- No requiere transacciones ACID
- Equipo tiene expertise en MongoDB
**Impacto:**
- Añade nueva tecnología al stack (+ complejidad operacional)
- Costos: +$2k/mes AWS DocumentDB
**Riesgos:**
- Curva de aprendizaje para resto del equipo
- Necesidad de mantener 2 tecnologías de DB
**Mitigación:**
- Limitar MongoDB solo a Notification Service
- Documentar best practices
- Training para equipo de ops
**Decisión ARB:** Aprobado con condiciones
- Condition 1: Usar AWS DocumentDB (managed) no MongoDB self-hosted
- Condition 2: Implementar backup automatizado
- Condition 3: Documentar operación en runbook
- Condition 4: Revisión en 6 meses para evaluar si se mantiene

Reporte de Conformidad (ejemplo mensual):

Periodo: Octubre 2024
Proyectos revisados: 4

| Proyecto              | Status     | Conformidad | Issues                          | Acción           |
|-----------------------|------------|-------------|---------------------------------|------------------|
| Score Engine ML       | In Progress| 95%         | Falta documentación de APIs     | Remediar Sem 42  |
| Payment Service       | Completed  | 100%        | Ninguno                         | -                |
| Fraud Detection       | Planning   | 90%         | Stack no estándar (propuesto Go)| ARB review Sem 43|
| Multi-region Setup    | In Progress| 85%         | Falta DR testing, IaC incompleto| Remediar Sem 44  |

Hallazgos críticos: 0
Hallazgos mayores: 2
Hallazgos menores: 5
Desviaciones aprobadas este mes: 1

Tendencia: ✓ Mejorando (vs mes anterior 82% conformidad promedio)
```

---

## Fase H - Gestión del Cambio de Arquitectura

### Objetivo
Asegurar que los cambios en la arquitectura sean gestionados de forma controlada y que la arquitectura siga siendo relevante.

### Actividades Clave
1. **Monitorear cambios del entorno**
   - Cambios en estrategia de negocio
   - Nuevas tecnologías emergentes
   - Cambios regulatorios
   - Feedback de implementación

2. **Evaluar impacto en arquitectura**
   - ¿Requiere cambios en arquitectura actual?
   - ¿Afecta decisiones previas?
   - ¿Genera nuevas oportunidades?

3. **Gestionar ciclo de vida de arquitectura**
   - Establecer proceso de revisión periódica
   - Definir triggers de actualización
   - Mantener documentación actualizada

4. **Lecciones aprendidas**
   - Capturar aprendizajes de implementación
   - Actualizar patrones y guías
   - Compartir conocimiento

### Artefactos Principales
- **Solicitud de Cambio de Arquitectura**: Propuesta formal de cambio
- **Evaluación de Impacto**: Análisis de cambios propuestos
- **Arquitectura Actualizada**: Documentos actualizados post-cambio
- **Registro de Lecciones Aprendidas**: Knowledge base de aprendizajes

### Ejemplo - Startup Fintech

```
Triggers de Revisión de Arquitectura:

**Programados:**
- Revisión trimestral ligera (sanity check)
- Revisión anual profunda (full ADM iteration)
- Post-mortem después de incidentes mayores
- Retrospectiva al finalizar cada proyecto mayor

**Ad-hoc (event-driven):**
- Cambio en estrategia de negocio (ej: nuevo mercado, nueva línea de producto)
- Nueva regulación que afecta arquitectura
- Adquisición/fusión con otra empresa
- Cambio tecnológico disruptivo (ej: nueva versión de AWS con capacidades críticas)
- Problemas de performance/escalabilidad no resueltos con arquitectura actual

Ejemplo de Solicitud de Cambio de Arquitectura:

**Título:** Migrar de scoring batch a scoring en tiempo real

**Contexto:**
- Actualmente el Score Engine procesa scoring cada 6 horas (batch)
- Negocio requiere aprobación instantánea (<5 segundos) para mejorar conversión
- Estudio de mercado muestra que competidores ofrecen aprobación en <10 segundos

**Cambios propuestos en arquitectura:**

1. **Cambio en Arquitectura de Aplicaciones:**
   - Convertir Score Engine de batch (Lambda diario) a streaming (ECS always-on)
   - Añadir cache de scoring (Redis) con TTL de 1 hora
   - Integrar llamada síncrona desde Lending Core API

2. **Cambio en Arquitectura de Datos:**
   - Añadir denormalización de datos de Bureau en cache
   - Implementar CDC (Change Data Capture) para mantener cache actualizado

3. **Cambio en Arquitectura Tecnológica:**
   - Escalar Score Engine horizontally (min 2, max 10 instancias)
   - Añadir Circuit Breaker para proteger Score Engine
   - Implementar fallback a scoring simplificado si Score Engine no responde

**Impacto:**

Positivo:
- Mejora conversión estimada en 20% (más clientes aprueban)
- Mejor experiencia de usuario
- Ventaja competitiva

Negativo:
- Incremento de costos: +$3k/mes (ECS always-on + cache)
- Incremento de complejidad operacional
- Dependencia crítica en tiempo real (si Score Engine cae, no se pueden aprobar solicitudes)

**Alternativas evaluadas:**

1. Mantener batch pero reducir frecuencia (cada 1h)
   - Pros: Bajo esfuerzo, bajo costo
   - Contras: No cumple requerimiento de <5 seg

2. Scoring en tiempo real híbrido (cache + async)
   - Pros: Balance costo-performance
   - Contras: Complejidad adicional

3. Scoring en tiempo real completo (propuesta recomendada)
   - Pros: Cumple requerimiento, simple
   - Contras: Mayor costo

**Riesgos:**
- R1: Latencia >5seg en percentil 95 → Mitigar con cache agresivo
- R2: Score Engine como punto único de falla → Mitigar con fallback
- R3: Costos mayores a estimado → Mitigar con auto-scaling optimizado

**Estimación:**
- Esfuerzo: 3 semanas (1 desarrollador)
- Costo implementación: $30k
- Incremento costo run rate: $3k/mes

**Decisión ARB:** Aprobado
**Responsable:** Tech Lead Backend
**Timeline:** Sprint 23-24 (Noviembre)

---

Lecciones Aprendidas - Proyecto Migración Cloud:

**Lo que funcionó bien:**

1. **Piloto con Analytics primero**
   - Aprendizaje: Empezar con workload no-crítico reduce riesgo y permite validar patrones
   - Acción: Estandarizar approach de "piloto primero" para futuras migraciones

2. **Blue-Green deployment**
   - Aprendizaje: Permitió cutover sin downtime y rollback rápido
   - Acción: Documentar como patrón estándar de migración

3. **Equipos cross-funcionales**
   - Aprendizaje: DevOps + Backend + DBA trabajando juntos aceleró resolución de problemas
   - Acción: Mantener estructura de equipos cross-funcionales

4. **IaC desde día 1**
   - Aprendizaje: Terraform permitió replicar entornos y reducir errores
   - Acción: Prohibir ClickOps, todo debe ser IaC

**Desafíos y aprendizajes:**

1. **Subestimamos esfuerzo de refactoring de monolito**
   - Problema: Estimamos 6 semanas, tomó 10 semanas
   - Root cause: Deuda técnica no documentada, dependencias ocultas
   - Acción: En futuras migraciones, dedicar 2 semanas a discovery/assessment profundo antes de estimar

2. **Problemas de latencia en integración con KYC provider**
   - Problema: Post-migración, latencia aumentó de 200ms a 1.2seg
   - Root cause: No consideramos latencia inter-region (KYC en us-west, nosotros en us-east)
   - Solución: Implementamos cache agresivo de resultados KYC
   - Acción: Evaluar latencias de integraciones externas en fase de diseño

3. **Costos AWS mayores a estimado inicial (25% más)**
   - Problema: Data transfer costs no considerados, over-provisioning inicial
   - Root cause: Falta de expertise en cost modeling de AWS
   - Solución: Implementamos FinOps, rightsizing de instancias
   - Acción: Contratar expertise en AWS cost optimization, implementar tagging estricto

4. **Resistencia del equipo de DBA a PostgreSQL**
   - Problema: DBAs con 10+ años de experiencia en Oracle resistieron cambio
   - Solución: Training formal, pair programming con DBAs junior que ya conocían PostgreSQL
   - Acción: En futuros cambios tecnológicos, plan de change management explícito

**Decisiones arquitecturales a revisar:**

1. **Re-evaluar uso de ECS vs EKS** (revisar en Q2 2025)
   - Contexto: Elegimos ECS por simplicidad, pero equipo ahora tiene más expertise
   - Considerar: ¿EKS nos daría más flexibilidad para multi-cloud?

2. **Re-evaluar necesidad de Service Mesh** (revisar en Q3 2025)
   - Contexto: No implementamos service mesh inicialmente por complejidad
   - Considerar: Con 15+ microservicios, ¿justifica observabilidad y traffic management?

**Mejoras a la arquitectura de referencia:**

1. Añadir patrón de "Strangler Fig" para migraciones de monolitos
2. Documentar patrones de caching (L1, L2, invalidation)
3. Añadir checklist de "Cloud Migration Readiness"
4. Crear template de "Well-Architected Review" basado en framework de AWS

**Métricas post-implementación (3 meses después):**

Objetivos vs Realidad:
- Reducción costos: Target 30%, Realidad 23% (parcial, mejorable con optimización)
- Disponibilidad: Target 99.9%, Realidad 99.95% (✓ superado)
- Time-to-deploy: Target <30min, Realidad 18min (✓ superado)
- Incidentes críticos: Target <2/mes, Realidad 0.7/mes (✓ superado)
- Expansión internacional: Target 2 regiones, Realidad 3 regiones (✓ superado)
```

---

## Gestión de Requerimientos

### Objetivo
Proceso continuo que asegura que los requerimientos de arquitectura se identifican, documentan, priorizan y rastrean a través de todo el ciclo ADM.

### Actividades Clave
1. **Identificar requerimientos**
   - Requerimientos de negocio (capacidades, procesos)
   - Requerimientos funcionales (features, integraciones)
   - Requerimientos no-funcionales (performance, seguridad, escalabilidad)
   - Constraints (regulatorios, presupuesto, tiempo)

2. **Documentar y priorizar**
   - Registrar en repositorio centralizado
   - Clasificar por tipo y criticidad
   - Validar con stakeholders

3. **Rastrear trazabilidad**
   - Vincular requerimientos con decisiones de arquitectura
   - Vincular decisiones con componentes/artefactos
   - Validar cobertura (todos los req. están addressados)

4. **Gestionar cambios**
   - Evaluar impacto de nuevos requerimientos
   - Re-priorizar según cambios de contexto
   - Comunicar cambios a stakeholders

### Artefactos Principales
- **Repositorio de Requerimientos**: Lista centralizada de todos los requerimientos
- **Matriz de Trazabilidad**: Mapeo requerimiento → decisión → artefacto
- **Registro de Cambios de Requerimientos**: Historial de cambios
- **Reporte de Cobertura**: Estado de implementación por requerimiento

### Ejemplo - Startup Fintech

```
Estructura de Requerimientos:

**BR - Business Requirements:**
- BR-001: Expandir a 5 países en 18 meses
- BR-002: Reducir tasa de rechazo de créditos del 40% al 25%
- BR-003: Procesar 10,000 solicitudes/día (vs 1,000 actual)
- BR-004: Reducir OPEX de infraestructura en 30%

**FR - Functional Requirements:**
- FR-001: Sistema debe aprobar/rechazar solicitud de crédito en <5 segundos
- FR-002: Sistema debe soportar múltiples métodos de pago (tarjeta, transferencia, wallet)
- FR-003: Sistema debe detectar fraude en tiempo real
- FR-004: Sistema debe generar reportes regulatorios automáticamente

**NFR - Non-Functional Requirements:**
- NFR-001: Disponibilidad 99.9% (máximo 43 minutos downtime/mes)
- NFR-002: Latencia API <500ms percentil 95
- NFR-003: Soportar 100,000 usuarios concurrentes
- NFR-004: Datos PII encriptados en reposo (AES-256) y tránsito (TLS 1.3)
- NFR-005: Cumplir PCI-DSS nivel 1
- NFR-006: GDPR compliant (right to be forgotten, data portability)
- NFR-007: Backup con RPO <15 minutos, RTO <4 horas
- NFR-008: Logs de auditoría inmutables por 7 años

**CON - Constraints:**
- CON-001: Presupuesto de implementación: $1.5M
- CON-002: Timeline: 12 meses para go-live
- CON-003: Equipo: máximo 10 personas
- CON-004: Regulación: Banco Central requiere datos en país de origen
- CON-005: Legacy: Integración con sistema de contabilidad SAP debe mantenerse

Matriz de Trazabilidad (ejemplo parcial):

| Req ID  | Requerimiento                          | Decisión Arquitectural                | Artefacto/Componente        | Fase | Status |
|---------|----------------------------------------|---------------------------------------|-----------------------------|------|--------|
| BR-001  | Expandir a 5 países                    | Multi-region AWS deployment           | Multi-region Architecture   | D    | ✓ Done |
| BR-002  | Reducir rechazo de créditos            | ML-based Score Engine                 | Score Engine Service        | C    | ✓ Done |
| BR-003  | 10k solicitudes/día                    | Auto-scaling ECS + cache              | ECS Config + ElastiCache    | D    | ✓ Done |
| FR-001  | Aprobar en <5seg                       | Scoring en tiempo real + cache        | Score Engine + Redis        | C    | ✓ Done |
| FR-002  | Múltiples métodos de pago              | Payment Service multi-provider        | Payment Service             | C    | ✓ Done |
| FR-003  | Detección de fraude tiempo real        | Event-driven fraud detection          | Fraud Detection Service     | C    | In Prog|
| FR-004  | Reportes regulatorios automáticos      | Data Lake + scheduled reports         | Analytics Platform          | C    | ✓ Done |
| NFR-001 | Disponibilidad 99.9%                   | Multi-AZ, redundancia, health checks  | AWS Multi-AZ config         | D    | ✓ Done |
| NFR-002 | Latencia <500ms p95                    | Cache, CDN, DB read replicas          | ElastiCache + CloudFront    | D    | ✓ Done |
| NFR-003 | 100k usuarios concurrentes             | Auto-scaling + load balancer          | ECS Auto-scaling + ALB      | D    | ✓ Done |
| NFR-004 | Encriptación PII                       | KMS encryption at rest + TLS          | KMS + ALB TLS config        | D    | ✓ Done |
| NFR-005 | PCI-DSS compliance                     | Tokenization, segmentación red        | Payment Service + VPC       | D    | ✓ Done |
| NFR-006 | GDPR compliance                        | Data retention policies, APIs         | Compliance Service          | C    | ✓ Done |
| NFR-007 | RPO 15min, RTO 4h                      | Continuous backup + DR multi-region   | RDS backup + DR setup       | D    | ✓ Done |
| NFR-008 | Logs inmutables 7 años                 | S3 Object Lock + Glacier              | Logging pipeline + S3       | D    | ✓ Done |
| CON-004 | Datos en país de origen                | Multi-region con data residency       | Multi-region Architecture   | D    | ✓ Done |
| CON-005 | Integración con SAP                    | SAP connector service                 | SAP Integration Service     | C    | ✓ Done |

Cambios de Requerimientos durante el proyecto:

**Cambio #1:**
- Fecha: Mes 5
- Requerimiento original: NFR-001 (99.9% disponibilidad)
- Cambio solicitado: Aumentar a 99.95% disponibilidad
- Rationale: Feedback de negocio - competidores tienen mejor SLA
- Impacto: Requiere multi-region activo-activo (vs activo-pasivo planeado)
- Decisión: Aprobado, implementar en Release 3
- Incremento de costo: +$5k/mes

**Cambio #2:**
- Fecha: Mes 7
- Requerimiento original: FR-002 (Stripe + PayPal como métodos de pago)
- Cambio solicitado: Añadir soporte para PIX (Brasil)
- Rationale: Expansión a Brasil (PIX es método de pago dominante)
- Impacto: Payment Service debe integrar con nuevo provider
- Decisión: Aprobado, implementar en Release 3
- Incremento de esfuerzo: +2 semanas

**Cambio #3:**
- Fecha: Mes 9
- Nuevo requerimiento: FR-005 (Soporte para Open Banking)
- Rationale: Nueva regulación en Colombia requiere Open Banking
- Impacto: Requiere nuevas APIs + cambios en autenticación
- Decisión: Aprobado pero diferido a Post-MVP (Release 5)
- Justificación: Timeline crítico, no es blocker para go-live

Reporte de Cobertura (ejemplo al finalizar proyecto):

Total de Requerimientos: 42
- Business Requirements: 8
- Functional Requirements: 15
- Non-Functional Requirements: 14
- Constraints: 5

Status:
- ✓ Implementados: 38 (90%)
- 🚧 En progreso: 2 (5%)
- ⏸️ Diferidos: 2 (5%)
- ❌ Rechazados: 0 (0%)

Requerimientos Diferidos:
- FR-005: Open Banking support (a Release 5, post-MVP)
- FR-012: Mobile app nativa (a Release 5, PWA es suficiente para MVP)

Cobertura por fase:
- Fase A (Visión): 8/8 req. addressados (100%)
- Fase B (Negocio): 12/12 req. addressados (100%)
- Fase C (Apps/Data): 18/20 req. addressados (90%, 2 diferidos)
- Fase D (Tech): 14/14 req. addressados (100%)

Requerimientos no-funcionales - Status:
- Performance: ✓ Cumple (latencia p95 450ms, target <500ms)
- Escalabilidad: ✓ Cumple (probado hasta 150k usuarios concurrentes)
- Disponibilidad: ✓ Cumple (99.96% en últimos 3 meses)
- Seguridad: ✓ Cumple (PCI-DSS certificado, GDPR compliant)
- Compliance: ✓ Cumple (auditoría aprobada)
```

---

## Mejores Prácticas Generales del ADM

### Iteración y Adaptación
- El ADM no es waterfall: iterar entre fases según necesidad
- Adaptar nivel de detalle al contexto (startup vs corporación)
- Validar con stakeholders al final de cada fase antes de continuar

### Documentación Lean
- Documentar lo justo y necesario
- Preferir diagramas simples sobre documentos extensos
- Mantener documentación actualizada (living documentation)

### Comunicación Multi-Nivel
- Ejecutivos: Visión, beneficios, ROI
- Negocio: Capacidades, procesos, cambios organizacionales
- Técnicos: Componentes, patrones, stack tecnológico
- Operaciones: Deployment, monitoreo, runbooks

### Gestión de Riesgos Continua
- Identificar riesgos en cada fase
- Priorizar por probabilidad e impacto
- Definir mitigaciones concretas
- Revisar riesgos periódicamente

### Value-Driven
- Priorizar por valor de negocio
- Identificar quick wins tempranos
- Medir beneficios realizados vs esperados
- Ajustar roadmap según feedback
