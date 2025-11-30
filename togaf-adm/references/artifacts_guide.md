# Guía de Artefactos TOGAF

Esta guía describe los principales artefactos que se generan durante el ciclo ADM, organizados por tipo: Catálogos, Matrices y Diagramas.

## Tabla de Contenidos
1. [Catálogos](#catálogos)
2. [Matrices](#matrices)
3. [Diagramas Descriptivos](#diagramas-descriptivos)
4. [Uso por Fase](#uso-por-fase)

---

## Catálogos

Los catálogos son listas estructuradas de elementos arquitecturales. Son el inventario fundamental de la arquitectura.

### Catálogo de Principios de Arquitectura

**Propósito:** Documentar los principios que guían todas las decisiones arquitecturales

**Cuándo usar:** Fase Preliminar

**Estructura:**
```
| ID   | Principio | Rationale | Implicaciones |
|------|-----------|-----------|---------------|
```

**Ejemplo:**
```markdown
| ID  | Principio                    | Rationale                                      | Implicaciones                                    |
|-----|------------------------------|------------------------------------------------|--------------------------------------------------|
| P01 | API-First                    | Toda funcionalidad debe ser reutilizable       | - Todas las features expuestas como APIs         |
|     |                              | por múltiples canales (web, mobile, partners)  | - Requiere diseño de APIs antes de UI            |
|     |                              |                                                | - Necesidad de API Gateway y gestión de versiones|
| P02 | Seguridad por diseño         | Proteger datos sensibles desde la concepción   | - Security reviews obligatorios                  |
|     |                              | no como afterthought                           | - Encriptación por defecto                       |
|     |                              |                                                | - Threat modeling en fase de diseño              |
| P03 | Buy over Build               | Preferir soluciones probadas del mercado       | - Evaluar SaaS antes de desarrollo custom        |
|     |                              | para acelerar time-to-market                   | - Menor control, mayor dependencia de vendors    |
|     |                              |                                                | - Ahorro en mantenimiento a largo plazo          |
```

---

### Catálogo de Stakeholders

**Propósito:** Identificar todas las partes interesadas y su relación con la arquitectura

**Cuándo usar:** Fase Preliminar, Fase A

**Estructura:**
```
| Stakeholder | Rol | Interés | Poder | Estrategia de Engagement |
|-------------|-----|---------|-------|--------------------------|
```

**Ejemplo:**
```markdown
| Stakeholder        | Rol                  | Interés | Poder | Estrategia de Engagement                    |
|--------------------|----------------------|---------|-------|---------------------------------------------|
| CEO                | Sponsor ejecutivo    | Alto    | Alto  | Manage Closely: Updates semanales, aprobar  |
|                    |                      |         |       | decisiones mayores                          |
| CTO                | Owner técnico        | Alto    | Alto  | Manage Closely: Participación activa en ARB |
| CFO                | Aproba presupuesto   | Medio   | Alto  | Keep Satisfied: Monthly business reviews    |
| CISO               | Seguridad/Compliance | Alto    | Medio | Manage Closely: Security reviews todas fases|
| VP Product         | Visión de producto   | Alto    | Medio | Manage Closely: Validar capacidades negocio |
| Tech Leads (5)     | Implementadores      | Alto    | Medio | Keep Informed: Design reviews, documentación|
| Regulador          | Compliance           | Medio   | Alto  | Keep Satisfied: Reportes de cumplimiento    |
| Usuarios finales   | Usan el sistema      | Alto    | Bajo  | Monitor: User research, feedback loops      |
```

---

### Catálogo de Capacidades de Negocio

**Propósito:** Listar las capacidades que la organización necesita para ejecutar su estrategia

**Cuándo usar:** Fase A, Fase B

**Estructura:**
```
| ID | Capacidad | Descripción | Nivel | Propietario | Estado AS-IS | Estado TO-BE | Gap |
|----|-----------|-------------|-------|-------------|--------------|--------------|-----|
```

**Ejemplo Fintech:**
```markdown
| ID    | Capacidad                      | Descripción                       | Nivel | Owner      | AS-IS      | TO-BE      | Gap      |
|-------|--------------------------------|-----------------------------------|-------|------------|------------|------------|----------|
| CAP01 | Originación de Créditos        | Captar y procesar solicitudes     | 1     | VP Lending | Nivel 2    | Nivel 4    | +2       |
| CAP02 | - Onboarding Digital           | Registro y KYC digital            | 2     | PM Digital | Nivel 2    | Nivel 4    | +2       |
| CAP03 | - Verificación de Identidad    | KYC/AML automático                | 2     | Compliance | Nivel 3    | Nivel 5    | +2       |
| CAP04 | - Scoring Crediticio           | Evaluación de riesgo              | 2     | Risk       | Nivel 1    | Nivel 5    | +4 (!)   |
| CAP05 | - Aprobación                   | Decisión de crédito               | 2     | Risk       | Manual     | Automática | CRÍTICO  |
| CAP06 | Procesamiento de Pagos         | Recibir y aplicar pagos           | 1     | VP Ops     | Nivel 3    | Nivel 4    | +1       |
| CAP07 | Gestión de Morosidad           | Detección y cobranza              | 1     | VP Ops     | Nivel 2    | Nivel 4    | +2       |
| CAP08 | Detección de Fraude            | Identificar patrones fraudulentos | 1     | CISO       | No existe  | Nivel 3    | CREAR    |

Niveles de Madurez:
0 = No existe
1 = Inicial/Ad-hoc
2 = Repetible pero manual
3 = Definido y documentado
4 = Gestionado y medido
5 = Optimizado y automatizado
```

---

### Catálogo de Procesos de Negocio

**Propósito:** Inventariar los procesos principales que ejecutan las capacidades

**Cuándo usar:** Fase B

**Estructura:**
```
| ID | Proceso | Descripción | Soporta Capacidad | Owner | Criticidad | Automatización AS-IS | Automatización TO-BE |
|----|---------|-------------|-------------------|-------|------------|---------------------|---------------------|
```

**Ejemplo:**
```markdown
| ID    | Proceso                   | Descripción                          | Capacidad | Owner   | Criticidad | Auto AS-IS | Auto TO-BE |
|-------|---------------------------|--------------------------------------|-----------|---------|------------|------------|------------|
| PR001 | Solicitud de Crédito      | Cliente solicita → decisión → firma  | CAP01     | Lending | ALTA       | 20%        | 90%        |
| PR002 | Verificación KYC          | Validar identidad del cliente        | CAP03     | Compl   | ALTA       | 50%        | 95%        |
| PR003 | Análisis de Riesgo        | Scoring y decisión de aprobación     | CAP04-05  | Risk    | CRÍTICA    | 10%        | 95%        |
| PR004 | Desembolso                | Transferir fondos aprobados          | CAP01     | Ops     | CRÍTICA    | 80%        | 95%        |
| PR005 | Procesamiento de Pago     | Cliente paga cuota                   | CAP06     | Ops     | CRÍTICA    | 90%        | 95%        |
| PR006 | Gestión de Mora           | Detectar + notificar + cobrar        | CAP07     | Ops     | ALTA       | 30%        | 80%        |
```

---

### Catálogo de Roles

**Propósito:** Definir los roles de negocio y sus responsabilidades

**Cuándo usar:** Fase B

**Estructura:**
```
| ID | Rol | Descripción | Responsabilidades | Participa en Procesos |
|----|-----|-------------|-------------------|-----------------------|
```

**Ejemplo:**
```markdown
| ID   | Rol                   | Descripción                        | Responsabilidades                      | Procesos              |
|------|-----------------------|------------------------------------|----------------------------------------|-----------------------|
| R001 | Cliente               | Usuario final que solicita crédito | - Proveer información                  | PR001, PR005          |
|      |                       |                                    | - Firmar contrato                      |                       |
|      |                       |                                    | - Realizar pagos                       |                       |
| R002 | Analista de Riesgo    | Revisa casos complejos             | - Analizar scoring atípico             | PR003                 |
|      |                       |                                    | - Aprobar/rechazar manualmente         |                       |
| R003 | Oficial de Compliance | Supervisa cumplimiento             | - Revisar alertas AML                  | PR002, PR003          |
|      |                       |                                    | - Aprobar casos de alto riesgo         |                       |
| R004 | Agente de Cobranza    | Gestiona morosidad                 | - Contactar clientes morosos           | PR006                 |
|      |                       |                                    | - Negociar reestructuraciones          |                       |
| R005 | Sistema (Automático)  | Procesamiento sin intervención     | - Scoring automático (90% casos)       | Todos                 |
|      |                       |                                    | - Notificaciones automáticas           |                       |
```

---

### Catálogo de Entidades de Datos

**Propósito:** Inventariar las entidades de datos críticas del negocio

**Cuándo usar:** Fase C (Datos)

**Estructura:**
```
| ID | Entidad | Descripción | Criticidad | Sensibilidad | Volumen | Retención | Owner |
|----|---------|-------------|------------|--------------|---------|-----------|-------|
```

**Ejemplo:**
```markdown
| ID   | Entidad             | Descripción                    | Criticidad | Sensibilidad | Volumen    | Retención | Owner      |
|------|---------------------|--------------------------------|------------|--------------|------------|-----------|------------|
| E001 | Cliente             | Datos personales del cliente   | CRÍTICA    | PII/Alta     | 100K       | 7 años    | Compliance |
| E002 | Solicitud de Crédito| Request de financiamiento      | CRÍTICA    | Media        | 500K       | 7 años    | Lending    |
| E003 | Score Crediticio    | Resultado de análisis de riesgo| ALTA       | Media        | 500K       | 7 años    | Risk       |
| E004 | Transacción         | Desembolsos y pagos            | CRÍTICA    | Alta         | 5M         | 10 años   | Finance    |
| E005 | Cuenta              | Cuenta activa de crédito       | CRÍTICA    | Alta         | 80K        | 10 años   | Finance    |
| E006 | Evento de Auditoría | Log inmutable de operaciones   | ALTA       | Media        | 50M        | 7 años    | Compliance |
| E007 | Documento KYC       | Documentos de identidad        | ALTA       | PII/Alta     | 200K files | 7 años    | Compliance |
| E008 | Regla de Negocio    | Políticas de scoring           | MEDIA      | Baja         | 500 rules  | Histórico | Risk       |
```

---

### Catálogo de Aplicaciones

**Propósito:** Inventariar todos los sistemas de software

**Cuándo usar:** Fase C (Aplicaciones)

**Estructura:**
```
| ID | Aplicación | Descripción | Tipo | Vendor | Estado | Soporta Capacidades | Criticidad |
|----|------------|-------------|------|--------|--------|---------------------|------------|
```

**Ejemplo:**
```markdown
| ID    | Aplicación            | Descripción               | Tipo       | Vendor    | Estado    | Capacidades       | Criticidad |
|-------|-----------------------|---------------------------|------------|-----------|-----------|-------------------|------------|
| APP01 | Customer Portal       | Portal web del cliente    | Custom SPA | In-house  | TO-BE     | CAP02, CAP01      | ALTA       |
| APP02 | Lending Core API      | Core de originación       | Custom API | In-house  | TO-BE     | CAP01-05, CAP06-07| CRÍTICA    |
| APP03 | Score Engine          | Motor de scoring ML       | Custom     | In-house  | TO-BE     | CAP04             | CRÍTICA    |
| APP04 | Payment Service       | Procesamiento de pagos    | Custom API | In-house  | TO-BE     | CAP06             | CRÍTICA    |
| APP05 | Compliance Service    | Auditoría y reglas        | Custom API | In-house  | TO-BE     | CAP03, CAP05      | ALTA       |
| APP06 | Notification Service  | Email/SMS/Push            | Custom     | In-house  | TO-BE     | Transversal       | MEDIA      |
| APP07 | Analytics Platform    | BI y reportes             | Hybrid     | Snowflake | TO-BE     | Transversal       | MEDIA      |
| APP08 | Stripe Integration    | Payment gateway           | SaaS       | Stripe    | TO-BE     | CAP06             | ALTA       |
| APP09 | Bureau de Crédito API | Consulta de score externo | SaaS       | Equifax   | AS-IS/TO-BE| CAP04            | ALTA       |
| APP10 | KYC Provider          | Verificación de identidad | SaaS       | Jumio     | TO-BE     | CAP03             | ALTA       |
| APP11 | Legacy Monolith       | Sistema actual PHP        | Custom     | In-house  | AS-IS     | Todos             | DEPRECAR   |
```

---

### Catálogo de Tecnologías

**Propósito:** Inventariar plataformas, frameworks y herramientas tecnológicas

**Cuándo usar:** Fase D

**Estructura:**
```
| ID | Tecnología | Tipo | Propósito | Versión | Estado | Vendor | Licencia |
|----|------------|------|-----------|---------|--------|--------|----------|
```

**Ejemplo:**
```markdown
| ID    | Tecnología       | Tipo            | Propósito               | Versión | Estado | Vendor    | Licencia    |
|-------|------------------|-----------------|-------------------------|---------|--------|-----------|-------------|
| T001  | AWS ECS          | Container       | Runtime de aplicaciones | Latest  | TO-BE  | AWS       | Commercial  |
| T002  | RDS PostgreSQL   | Database        | Base de datos principal | 15.x    | TO-BE  | AWS       | Commercial  |
| T003  | ElastiCache Redis| Cache           | Cache de aplicación     | 7.x     | TO-BE  | AWS       | Commercial  |
| T004  | S3               | Object Storage  | Archivos y data lake    | Latest  | TO-BE  | AWS       | Commercial  |
| T005  | API Gateway      | API Management  | Gestión de APIs         | Latest  | TO-BE  | AWS       | Commercial  |
| T006  | CloudFront       | CDN             | Distribución frontend   | Latest  | TO-BE  | AWS       | Commercial  |
| T007  | MSK (Kafka)      | Streaming       | Event streaming         | 3.x     | TO-BE  | AWS       | Commercial  |
| T008  | Lambda           | Serverless      | Funciones event-driven  | Latest  | TO-BE  | AWS       | Commercial  |
| T009  | Node.js          | Runtime         | Backend APIs            | 20 LTS  | TO-BE  | OpenJS    | MIT         |
| T010  | Python           | Language        | ML y data processing    | 3.11    | TO-BE  | PSF       | Open Source |
| T011  | React            | Frontend        | UI framework            | 18.x    | TO-BE  | Meta      | MIT         |
| T012  | Terraform        | IaC             | Infraestructura         | 1.5+    | TO-BE  | HashiCorp | MPL 2.0     |
| T013  | GitHub Actions   | CI/CD           | Pipeline automatizado   | Latest  | TO-BE  | GitHub    | Commercial  |
| T014  | Datadog          | Observability   | Monitoring y APM        | Latest  | TO-BE  | Datadog   | Commercial  |
| T015  | Oracle DB        | Database        | Base de datos legacy    | 12c     | AS-IS  | Oracle    | DEPRECAR    |
```

---

## Matrices

Las matrices relacionan diferentes elementos arquitecturales para mostrar dependencias, asignaciones y gaps.

### Matriz Proceso-Rol (RACI)

**Propósito:** Definir responsabilidades en cada proceso

**Cuándo usar:** Fase B

**Estructura:**
```
R = Responsible (ejecuta)
A = Accountable (aprueba/responsable final)
C = Consulted (consultado)
I = Informed (informado)
```

**Ejemplo:**
```markdown
| Proceso                | Cliente | Analista Riesgo | Oficial Compliance | Sistema | VP Lending |
|------------------------|---------|-----------------|--------------------|---------| -----------|
| Solicitud de Crédito   | R       | I               | I                  | R       | A          |
| Verificación KYC       | C       | I               | A                  | R       | I          |
| Análisis de Riesgo     | I       | A/R (casos      | C (alto riesgo)    | R (90%) | I          |
|                        |         | complejos)      |                    |         |            |
| Desembolso             | I       | I               | I                  | R       | A          |
| Procesamiento de Pago  | R       | I               | I                  | R       | I          |
| Gestión de Mora        | C       | I               | I                  | R       | A          |
```

---

### Matriz Capacidad-Aplicación

**Propósito:** Mapear qué aplicaciones soportan qué capacidades de negocio

**Cuándo usar:** Fase C

**Ejemplo:**
```markdown
| Capacidad              | Portal | Lending Core | Score Engine | Payment Svc | Compliance Svc |
|------------------------|--------|--------------|--------------|-------------|----------------|
| Onboarding Digital     | ✓      | ✓            |              |             |                |
| Verificación Identidad |        | ✓            |              |             | ✓              |
| Scoring Crediticio     |        | ✓            | ✓            |             |                |
| Aprobación             |        | ✓            | ✓            |             | ✓              |
| Desembolso             |        | ✓            |              | ✓           |                |
| Procesamiento Pagos    | ✓      | ✓            |              | ✓           |                |
| Gestión Morosidad      | ✓      | ✓            |              |             |                |
| Detección Fraude       |        | ✓            |              |             | ✓              |
```

**Análisis:**
- Lending Core es el sistema más acoplado (soporta casi todas las capacidades) → posible candidato para refactoring
- Score Engine es especializado (una sola capacidad)
- Portal tiene cobertura limitada (solo interacción con cliente)

---

### Matriz Aplicación-Dato

**Propósito:** Identificar qué aplicación es dueña (Create/Update/Delete) vs consume (Read) cada entidad de datos

**Cuándo usar:** Fase C

**Leyenda:**
- C = Create
- R = Read
- U = Update
- D = Delete

**Ejemplo:**
```markdown
| Aplicación          | Cliente | Solicitud | Score | Transacción | Cuenta | Auditoría |
|---------------------|---------|-----------|-------|-------------|--------|-----------|
| Customer Portal     | C       | C, R      | R     | R           | R      | -         |
| Lending Core API    | R, U    | CRUD      | R     | CRUD        | CRUD   | C         |
| Score Engine        | R       | R         | CRUD  | -           | R      | C         |
| Payment Service     | R       | R         | -     | CRUD        | R, U   | C         |
| Compliance Service  | R       | R         | R     | R           | R      | R         |
| Analytics Platform  | R       | R         | R     | R           | R      | R         |
```

**Análisis:**
- Lending Core es owner de demasiadas entidades → refactorizar en microservicios más granulares
- Evento de Auditoría es write-only para servicios, read-only para Analytics (patrón CQRS)

---

### Matriz Aplicación-Tecnología

**Propósito:** Documentar el stack tecnológico de cada aplicación

**Cuándo usar:** Fase D

**Ejemplo:**
```markdown
| Aplicación          | Compute    | Database     | Cache       | Integration      | Language |
|---------------------|------------|--------------|-------------|------------------|----------|
| Customer Portal     | S3+CF      | -            | -           | API Gateway      | React    |
| Lending Core API    | ECS        | RDS PG       | Redis       | ALB+EventBridge  | Node.js  |
| Score Engine        | ECS+Lambda | RDS Read Rep | Redis       | MSK+EventBridge  | Python   |
| Payment Service     | ECS        | RDS PG       | Redis       | ALB+SQS          | Java     |
| Compliance Service  | ECS        | RDS PG       | -           | EventBridge      | Go       |
| Notification Svc    | Lambda     | DynamoDB     | -           | SNS+SQS          | Node.js  |
| Analytics Platform  | Glue       | S3+Snowflake | -           | S3 Events        | SQL+dbt  |
```

---

### Matriz de Análisis de Brechas

**Propósito:** Consolidar todas las brechas entre AS-IS y TO-BE

**Cuándo usar:** Fases B, C, D, E

**Ejemplo:**
```markdown
| ID  | Brecha                              | Tipo    | AS-IS           | TO-BE                | Impacto | Esfuerzo | Prioridad |
|-----|-------------------------------------|---------|-----------------|----------------------|---------|----------|-----------|
| G01 | Scoring manual                      | Proceso | Excel manual    | ML automático        | Alto    | Alto     | CRÍTICO   |
| G02 | Monolito no escalable               | App     | PHP monolito    | Microservicios ECS   | Alto    | Alto     | CRÍTICO   |
| G03 | Base de datos on-premise            | Tech    | Oracle on-prem  | RDS PostgreSQL cloud | Alto    | Alto     | CRÍTICO   |
| G04 | Sin detección de fraude             | Cap     | No existe       | ML fraud detection   | Alto    | Medio    | ALTO      |
| G05 | API Gateway inexistente             | Tech    | Acceso directo  | AWS API Gateway      | Medio   | Bajo     | ALTO      |
| G06 | Observabilidad limitada             | Tech    | Logs básicos    | Datadog APM          | Medio   | Medio    | MEDIO     |
| G07 | Infraestructura manual              | Tech    | ClickOps        | Terraform IaC        | Medio   | Medio    | MEDIO     |
| G08 | Payment provider único              | App     | Solo Stripe     | Multi-provider       | Bajo    | Bajo     | BAJO      |
```

---

### Matriz de Dependencias

**Propósito:** Identificar dependencias entre paquetes de trabajo o proyectos

**Cuándo usar:** Fase E, F

**Ejemplo:**
```markdown
| Proyecto          | Release 1 | Release 2 | Release 3 | Release 4 |
|-------------------|-----------|-----------|-----------|-----------|
| Release 1: Base   | -         | BLOCK     | BLOCK     | BLOCK     |
| Release 2: Core   |           | -         | BLOCK     | BLOCK     |
| Release 3: Adv    |           |           | -         | ENABLE    |
| Release 4: Opt    |           |           |           | -         |

Leyenda:
- BLOCK: Debe completarse antes de empezar
- ENABLE: Habilita pero no bloquea
- INFORM: Solo información, sin dependencia técnica
```

---

### Matriz de Riesgos vs Mitigaciones

**Propósito:** Documentar riesgos y sus mitigaciones

**Cuándo usar:** Todas las fases, especialmente E y F

**Ejemplo:**
```markdown
| ID  | Riesgo                           | Prob  | Impacto | Expo | Mitigación                              | Owner   | Estado    |
|-----|----------------------------------|-------|---------|------|-----------------------------------------|---------|-----------|
| R01 | Downtime en cutover              | Media | Alto    | 6    | Blue-green deploy, rollback plan        | DevOps  | Mitigado  |
| R02 | Pérdida de datos en migración    | Baja  | Crít    | 6    | Backups múltiples, validación checksums | DBA     | Mitigado  |
| R03 | Performance post-migración       | Media | Alto    | 6    | Load testing, auto-scaling              | Arch    | Mitigado  |
| R04 | Sobrecosto AWS                   | Alta  | Medio   | 6    | FinOps, alertas billing, reserved inst  | FinOps  | En proceso|
| R05 | Equipo sin expertise AWS         | Alta  | Medio   | 6    | Contratar 2 engineers, training         | CTO     | Mitigado  |
| R06 | Resistencia al cambio            | Media | Medio   | 4    | Change management, comunicación         | PM      | En proceso|

Exposición (Expo) = Probabilidad × Impacto
Probabilidad: Baja=1, Media=2, Alta=3
Impacto: Bajo=1, Medio=2, Alto=3, Crítico=4
```

---

## Diagramas Descriptivos

Los diagramas visualizan relaciones y flujos. En formato texto, describimos qué debe contener cada diagrama.

### Diagrama de Arquitectura de Negocio

**Propósito:** Mostrar capacidades, procesos, actores y sus relaciones

**Cuándo usar:** Fase B

**Qué incluir:**
- Capacidades de negocio (cajas agrupadas por nivel)
- Procesos principales (flujos entre capacidades)
- Actores/Roles (íconos de personas)
- Flujos de información (flechas)

**Descripción textual ejemplo:**
```
[Cliente] → Solicita crédito → [Onboarding Digital] → [Verificación KYC]
                                      ↓
                            [Análisis de Riesgo] → [Score Crediticio]
                                      ↓
                              [Aprobación Automática]
                                      ↓
                            [Firma Electrónica] → [Desembolso]
                                      ↓
                                  [Cuenta]
                                      ↓
             [Cliente] ← Recibe fondos ← [Procesamiento de Pagos]
```

---

### Diagrama de Arquitectura de Datos

**Propósito:** Mostrar entidades principales y sus relaciones (modelo lógico)

**Cuándo usar:** Fase C

**Descripción textual ejemplo:**
```
[Cliente] 1---M [Solicitud] M---1 [Score]
             |
             1
             |
             M
        [Cuenta] 1---M [Transacción]
             |
             1
             |
             M
      [Documento KYC]
```

---

### Diagrama de Arquitectura de Aplicaciones

**Propósito:** Mostrar componentes de aplicación y sus integraciones

**Cuándo usar:** Fase C

**Descripción textual ejemplo:**
```
[Cliente Web] → [CloudFront] → [S3: React SPA]
                                     ↓
                              [API Gateway]
                                     ↓
                      [ALB] → [Lending Core API (ECS)]
                                     ↓
                    ┌────────────────┼────────────────┐
                    ↓                ↓                ↓
          [Score Engine]    [Payment Service]  [Compliance Svc]
              (ECS)              (ECS)              (ECS)
                ↓                  ↓                  ↓
          [RDS PostgreSQL] ← [ElastiCache Redis] → [Event Bus]
                ↓
          [Data Lake S3] → [Snowflake Analytics]

Integraciones externas:
- Score Engine → Bureau de Crédito API
- Payment Service → Stripe API
- Compliance Svc → KYC Provider (Jumio)
```

---

### Diagrama de Arquitectura Tecnológica

**Propósito:** Mostrar infraestructura física/lógica (redes, servidores, plataformas)

**Cuándo usar:** Fase D

**Descripción textual ejemplo:**
```
AWS us-east-1
├── VPC (10.0.0.0/16)
│   ├── Public Subnet (10.0.1.0/24)
│   │   ├── NAT Gateway
│   │   └── ALB
│   ├── Private Subnet - App (10.0.10.0/24)
│   │   ├── ECS Cluster (Fargate)
│   │   │   ├── Lending Core (3 tasks)
│   │   │   ├── Score Engine (2 tasks)
│   │   │   ├── Payment Service (2 tasks)
│   │   │   └── Compliance Service (2 tasks)
│   │   └── ElastiCache Redis (cluster mode)
│   └── Private Subnet - Data (10.0.20.0/24)
│       └── RDS PostgreSQL (Multi-AZ)
│           ├── Primary (AZ-a)
│           └── Standby (AZ-b)
├── S3 Buckets
│   ├── Frontend assets (+ CloudFront)
│   ├── Data Lake (raw/processed/curated)
│   └── Backups (lifecycle → Glacier)
└── EventBridge → Lambda → SNS/SQS

Multi-region DR:
AWS eu-west-1 (standby)
└── RDS read replica + infra dormant (activable en 4h)
```

---

### Diagrama de Roadmap / Plan de Migración

**Propósito:** Visualizar secuencia temporal de paquetes de trabajo

**Cuándo usar:** Fase F

**Descripción textual ejemplo:**
```
Q1 2024          Q2 2024              Q3 2024              Q4 2024
│                │                    │                    │
├─ Release 1 ────┤                    │                    │
│  (Base AWS)    │                    │                    │
│                ├─── Release 2 ──────┤                    │
│                │    (Core Migr)     │                    │
│                │                    ├─── Release 3 ──────┤
│                │                    │    (Capacidades)   │
│                │                    │                    ├─ Release 4 ───┤
│                │                    │                    │  (Optimiz)     │
│                │                    │                    │                │
Milestone 1      Milestone 2          Milestone 3          Milestone 4 (Go-live)
```

---

## Uso por Fase

### Fase Preliminar
- Catálogo de Principios ✓
- Catálogo de Stakeholders ✓

### Fase A - Visión
- Catálogo de Capacidades (alto nivel) ✓
- Catálogo de Stakeholders (refinado) ✓
- Matriz de Stakeholders vs Capacidades ✓
- Diagrama de Arquitectura Baseline (AS-IS) ✓
- Diagrama de Arquitectura Target (TO-BE) ✓

### Fase B - Negocio
- Catálogo de Capacidades (detallado) ✓
- Catálogo de Procesos ✓
- Catálogo de Roles ✓
- Matriz Proceso-Rol (RACI) ✓
- Matriz Capacidad-Proceso ✓
- Diagrama de Procesos de Negocio ✓
- Análisis de Brechas de Negocio ✓

### Fase C - Sistemas de Información
- Catálogo de Entidades de Datos ✓
- Catálogo de Aplicaciones ✓
- Matriz Aplicación-Capacidad ✓
- Matriz Aplicación-Proceso ✓
- Matriz Aplicación-Dato ✓
- Diagrama de Arquitectura de Datos ✓
- Diagrama de Arquitectura de Aplicaciones ✓
- Análisis de Brechas de Datos ✓
- Análisis de Brechas de Aplicaciones ✓

### Fase D - Tecnología
- Catálogo de Tecnologías ✓
- Matriz Aplicación-Tecnología ✓
- Diagrama de Arquitectura Tecnológica ✓
- Análisis de Brechas Tecnológicas ✓

### Fase E - Oportunidades y Soluciones
- Análisis Consolidado de Brechas ✓
- Catálogo de Paquetes de Trabajo ✓
- Matriz de Dependencias ✓
- Matriz de Riesgos vs Mitigaciones ✓

### Fase F - Plan de Migración
- Roadmap (Diagrama de Plan de Migración) ✓
- Matriz de Transición (AS-IS → TO-BE por componente) ✓
- Plan de Recursos ✓
- Presupuesto ✓

### Fase G - Gobernanza
- Reporte de Conformidad ✓
- Registro de Desviaciones ✓

### Fase H - Gestión del Cambio
- Registro de Lecciones Aprendidas ✓
- Arquitectura Actualizada (todos los artefactos actualizados)
