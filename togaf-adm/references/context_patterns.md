# Patrones de Contexto para TOGAF ADM

Esta guía proporciona patrones y consideraciones específicas para aplicar el ADM en diferentes contextos y escenarios comunes.

## Tabla de Contenidos
1. [Startup Fintech](#startup-fintech)
2. [Migración a Cloud](#migración-a-cloud)
3. [Transformación Digital](#transformación-digital)
4. [Modernización de Legacy](#modernización-de-legacy)
5. [Expansión Internacional](#expansión-internacional)
6. [Fusión y Adquisición](#fusión-y-adquisición)

---

## Startup Fintech

### Contexto
Empresa emergente en sector financiero-tecnológico, típicamente con:
- Equipo pequeño (10-50 personas)
- Presión por time-to-market
- Restricciones regulatorias estrictas (PCI-DSS, GDPR, reguladores financieros)
- Necesidad de escalar rápidamente
- Cultura tech-first

### Consideraciones Clave

**Fase Preliminar:**
- **Principios críticos:**
  - Seguridad y compliance desde el diseño (no negociable)
  - Buy over Build (maximizar uso de SaaS para no-diferenciadores)
  - Cloud-native desde día 1
  - API-first para habilitar ecosistema

- **Governance ligero pero efectivo:**
  - ARB semanal de 1h (no comités pesados)
  - CTO como Architecture Owner
  - Revisiones de seguridad obligatorias pero rápidas

**Fase A - Visión:**
- **Enfoque:** Visión ambiciosa pero MVP viable
- **Drivers de negocio típicos:**
  - Captar X clientes en Y meses
  - Lanzar producto mínimo en Z semanas
  - Pasar auditorías regulatorias
  - Levantar siguiente ronda de inversión

- **Capacidades críticas a priorizar:**
  - Originación digital de clientes (KYC/AML automatizado)
  - Core transaccional básico
  - Cumplimiento regulatorio básico
  - Reporting para regulador e inversionistas

**Fase B - Negocio:**
- **Evitar:**
  - Sobre-diseñar procesos de back-office
  - Documentar procesos que aún no existen

- **Priorizar:**
  - Customer journey end-to-end
  - Procesos que tocan regulador
  - Procesos que no escalan (identificar cuellos de botella tempranos)

**Fase C - Sistemas:**
- **Arquitectura de Datos:**
  - Modelo simple pero extensible
  - Separar datos regulados (PII, transaccional) de analytics desde día 1
  - Event sourcing para auditoría (inmutabilidad)

- **Arquitectura de Aplicaciones:**
  - Monolito modular inicial aceptable (no forzar microservicios prematuramente)
  - Pero: diseñar bounded contexts claros desde inicio
  - API Gateway desde día 1 (aunque sea un solo backend)

- **Decisiones Build vs Buy:**
  - BUILD: Core de negocio diferenciador (ej: motor de scoring, risk engine)
  - BUY: Infraestructura (auth, payments, notifications, analytics)

**Fase D - Tecnología:**
- **Stack recomendado:**
  - Cloud: AWS/GCP/Azure (managed services al máximo)
  - Compute: Contenedores managed (ECS/Cloud Run) o serverless
  - DB: Managed PostgreSQL/Aurora (ACID), no bases exóticas
  - Cache: Redis managed
  - Observability: Datadog/New Relic (no montar Prometheus/Grafana)
  - IaC: Terraform desde día 1

- **Anti-patrones a evitar:**
  - Kubernetes prematuro (overhead operacional enorme)
  - Self-hosting de bases de datos
  - Infraestructura on-premise
  - Technology diversity sin razón (un lenguage backend es suficiente)

**Fase E-F - Roadmap:**
- **Priorización:**
  - Wave 1: MVP regulatorio (compliance + seguridad básica)
  - Wave 2: Core transaccional estable
  - Wave 3: Capacidades diferenciadoras (ML, analytics avanzado)
  - Wave 4: Optimización y scale

- **Criterios de Go/No-Go:**
  - Seguridad: 0 vulnerabilidades críticas
  - Compliance: Aprobación de oficial de compliance
  - Performance: Cumple SLA mínimo
  - NO esperar perfección: iterar rápido

**Fase G - Governance:**
- **Lightweight pero no skippear:**
  - Security review obligatorio en cada release
  - Code review por pares
  - Automated testing (unit + integration)
  - Cambios de arquitectura aprobados por CTO

**Riesgos Específicos:**
| Riesgo                              | Mitigación                                  |
|-------------------------------------|---------------------------------------------|
| Fallar auditoría regulatoria        | Contratar compliance expert, auditorías mock|
| Brecha de seguridad (catastrófico)  | Pentest regular, bug bounty, SOC2           |
| No escalar ante crecimiento explosivo| Load testing, auto-scaling, chaos engineering|
| Deuda técnica inmanejable           | Refactoring continuo (20% del tiempo)       |
| Vendor lock-in crítico              | Abstracciones, evitar features muy específicas|

---

## Migración a Cloud

### Contexto
Organización con infraestructura on-premise que migra a cloud (AWS/Azure/GCP), típicamente:
- Legacy de 5-15 años
- Aplicaciones monolíticas
- Equipos con skills tradicionales (no cloud-native)
- Presión por reducir CAPEX y mejorar agilidad

### Estrategias de Migración (6 Rs)

**1. Rehost (Lift & Shift):**
- **Qué:** Migrar VMs tal cual a cloud (EC2, Azure VMs)
- **Cuándo:** Migración rápida, baja transformación
- **Pros:** Rápido, bajo riesgo técnico
- **Contras:** No aprovecha beneficios cloud, costos altos
- **Ejemplo:** VM Oracle en data center → RDS Oracle en cloud

**2. Replatform (Lift & Reshape):**
- **Qué:** Migrar con optimizaciones menores (managed services)
- **Cuándo:** Balance entre velocidad y mejora
- **Pros:** Mejora operacional, reduce overhead
- **Contras:** Requiere cambios menores en app
- **Ejemplo:** SQL Server en VM → RDS SQL Server

**3. Repurchase (Replace):**
- **Qué:** Reemplazar con SaaS
- **Cuándo:** Solución comercial superior existe
- **Pros:** Sin mantenimiento, features modernas
- **Contras:** Migración de datos, cambio de procesos
- **Ejemplo:** Exchange Server → Office 365

**4. Refactor (Re-architect):**
- **Qué:** Rediseñar para cloud-native
- **Cuándo:** Maximizar beneficios cloud, apps críticas
- **Pros:** Máximo aprovechamiento de cloud
- **Contras:** Alto esfuerzo, alto riesgo
- **Ejemplo:** Monolito → Microservicios + contenedores

**5. Retire:**
- **Qué:** Apagar aplicaciones obsoletas
- **Cuándo:** App no usada o redundante
- **Pros:** Reduce complejidad y costo
- **Contras:** Validar dependencias ocultas

**6. Retain (Revisit):**
- **Qué:** Dejar on-premise temporalmente
- **Cuándo:** Migrarlasería muy complejo o riesgoso ahora
- **Pros:** Reduce riesgo, permite enfoque
- **Contras:** Infraestructura híbrida (complejidad)

### Patrón de Aplicación ADM

**Fase A - Visión:**
- **Assessment detallado del portfolio:**
  - Inventariar TODAS las aplicaciones (descubrir shadow IT)
  - Clasificar por estrategia de migración (6 Rs)
  - Identificar dependencias (mapping de integraciones)

- **Business case:**
  - Calcular TCO on-premise vs cloud (5 años)
  - Estimar costos de migración
  - Definir beneficios esperados (no solo costo: agilidad, resiliencia, scale)

**Fase B-C-D - Diseño:**
- **Aplicación por aplicación:**
  - Para cada app a migrar: AS-IS → estrategia (Rehost/Replatform/etc) → TO-BE
  - Identificar refactoring necesario
  - Diseñar coexistencia temporal on-prem + cloud

- **Patrones de integración híbrida:**
  - VPN/Direct Connect entre on-prem y cloud
  - API Gateway como punto de integración
  - Data replication (para DBs)

**Fase E - Waves de Migración:**
- **Wave 0 - Piloto:**
  - App no-crítica (ej: entorno dev/test o app interna)
  - Validar patrones, tooling, procesos
  - Lecciones aprendidas antes de apps críticas

- **Wave 1 - Quick Wins:**
  - Apps con Rehost/Replatform simple
  - Generar momentum y confianza

- **Wave 2-N - Core:**
  - Apps críticas con más transformación
  - En orden de dependencias

- **Wave Final - Cleanup:**
  - Apagar on-premise
  - Descomisionar data centers

**Fase F - Plan de Cutover:**
- **Estrategia por aplicación:**
  - Blue-green deployment (nuevo en cloud + viejo on-prem coexisten)
  - Canary/phased rollout (migrar tráfico gradualmente)
  - Big bang (switch en ventana de mantenimiento)

- **Sincronización de datos:**
  - Replicación continua on-prem → cloud
  - Cutover final: sync final + switch
  - Rollback plan: revertir a on-prem

**Fase G - Governance:**
- **Cloud Center of Excellence (CCoE):**
  - Equipo que define estándares cloud
  - Provee training, templates, best practices
  - Revisa arquitecturas de cada wave

- **FinOps desde día 1:**
  - Tagging de recursos
  - Alertas de costos
  - Rightsizing continuo

**Riesgos y Mitigaciones:**
| Riesgo                               | Mitigación                                        |
|--------------------------------------|---------------------------------------------------|
| Downtime inaceptable en cutover      | Blue-green, replicación, ventana de mant extendida|
| Sobrecostos cloud                    | FinOps, cost modeling previo, reserved instances  |
| Performance degradation              | Load testing previo, oversizing inicial luego optimize|
| Dependencias ocultas rompen          | Discovery exhaustivo, testing integrado           |
| Skills gap en equipo                 | Training, contratar cloud engineers, partners     |
| Data loss durante migración          | Backups múltiples, validación checksums, DR       |
| Complejidad operacional híbrida      | Minimizar período híbrido, automatizar todo       |

**Métricas de Éxito:**
- % de workloads migrados (objetivo: 80-90%, algunos pueden quedarse on-prem)
- Reducción de costos operativos (objetivo típico: 20-40%)
- Mejora en disponibilidad (objetivo: +0.5% uptime)
- Reducción en time-to-deploy (objetivo: 50% más rápido)
- Reducción en incidentes (objetivo: -30%)

---

## Transformación Digital

### Contexto
Organización tradicional que adopta tecnologías digitales para transformar operación y propuesta de valor:
- Empresa establecida (no startup)
- Procesos manuales o semi-automatizados
- Presión competitiva de disruptores digitales
- Necesidad de nueva customer experience

### Drivers Típicos
- **Customer Experience:** Ofrecer canales digitales (web, mobile, chatbot)
- **Eficiencia Operacional:** Automatizar procesos manuales
- **Nuevos Modelos de Negocio:** Plataformas, subscripciones, ecosistemas
- **Data-Driven:** Tomar decisiones basadas en datos y analytics
- **Agilidad:** Reducir time-to-market de nuevos productos/features

### Patrón de Aplicación ADM

**Fase A - Visión:**
- **Definir ambición digital:**
  - ¿Transformación incremental o disruptiva?
  - ¿Qué capacidades digitales son estratégicas?
  - ¿Qué experiencias del cliente cambiarán?

- **Assessment de madurez digital:**
  - Evaluar madurez actual (procesos, tecnología, cultura, skills)
  - Identificar gaps vs competidores digitales
  - Definir estado TO-BE de madurez

**Fase B - Negocio:**
- **Rediseñar customer journeys:**
  - Mapear journeys actuales (identificar pain points)
  - Diseñar journeys digitales (omnichannel, self-service, personalización)
  - Identificar touchpoints digitales necesarios

- **Transformar procesos:**
  - Priorizar procesos con mayor impacto en CX o costos
  - Automatizar con RPA, workflows, AI
  - Eliminar pasos que no aportan valor (no solo automatizar lo malo)

**Fase C - Sistemas:**
- **Arquitectura orientada a experiencia digital:**
  - **Capa de Experiencia:** Web apps, mobile apps, chatbots
  - **Capa de Orquestación:** API Gateway, BFF (Backend for Frontend)
  - **Capa de Capacidades:** Microservicios de negocio
  - **Capa de Sistemas de Record:** Legacy systems (envueltos en APIs)

- **Integración con Legacy:**
  - Patrón **Strangler Fig:** Nuevas capacidades en digital, gradualmente reemplazar legacy
  - APIs sobre legacy (wrappers)
  - ETL/ESB para sincronizar datos

**Fase D - Tecnología:**
- **Plataformas digitales:**
  - **Customer Data Platform (CDP):** Vista unificada de cliente
  - **Content Management System (CMS):** Gestión de contenido digital
  - **Commerce Platform:** E-commerce
  - **Analytics Platform:** BI, ML, AI
  - **Engagement Platform:** Marketing automation, CRM

- **Infraestructura:**
  - Cloud para agilidad (nueva apps en cloud)
  - APIs y microservicios para desacoplamiento
  - DevOps y CI/CD para velocidad

**Fase E - Roadmap:**
- **Enfoque por oleadas temáticas:**
  - **Wave 1: Digital Foundation**
    - Customer portal básico
    - APIs sobre sistemas core
    - Analytics básico

  - **Wave 2: Customer Experience**
    - Mobile app
    - Personalización
    - Omnichannel

  - **Wave 3: Automation**
    - RPA para back-office
    - Chatbots
    - Workflows automatizados

  - **Wave 4: Intelligence**
    - AI/ML para recomendaciones
    - Predictive analytics
    - Autoservicio inteligente

**Cambio Organizacional (crítico):**
- **Cultura:** De jerárquica/waterfall a ágil/iterativa
- **Skills:** Upskilling en digital (UX, APIs, cloud, data science)
- **Estructura:** Equipos cross-funcionales orientados a producto
- **Métricas:** De output (features entregadas) a outcome (valor de negocio)

**Riesgos:**
| Riesgo                                | Mitigación                                     |
|---------------------------------------|------------------------------------------------|
| Resistencia al cambio organizacional  | Change management, quick wins visibles, sponsors|
| Legacy bloquea agilidad               | APIs sobre legacy, strangler pattern           |
| Proyectos digitales como IT initiatives| Business ownership, equipos de negocio+IT      |
| Falta de skills digitales             | Contratar, training, partners                  |
| Brecha digital entre generaciones     | UX simple, múltiples canales (no solo digital) |

---

## Modernización de Legacy

### Contexto
Actualizar sistemas legacy (mainframe, AS/400, monolitos antiguos) que son críticos pero dificultan innovación.

### Patrón Strangler Fig

**Concepto:** Gradualmente reemplazar legacy construyendo nuevo sistema alrededor, estrangulando el antiguo.

**Fases:**
1. **Transform:** Crear nuevo servicio para una capacidad
2. **Co-exist:** Nuevo y legacy coexisten, routing inteligente
3. **Eliminate:** Cuando legacy ya no tiene funcionalidad, apagar

**Aplicación en ADM:**

**Fase B-C:** Identificar seams (costuras) en el legacy donde cortar
- Analizar bounded contexts de negocio
- Identificar qué módulos son más independientes
- Priorizar por valor de negocio y facilidad de extracción

**Fase D:** Estrategia de coexistencia
```
[Frontend] → [API Gateway/Facade]
                     ↓
        ┌────────────┴────────────┐
        ↓                         ↓
[Nuevo Microservicio]      [Legacy System]
        ↓                         ↓
[Nueva DB]                   [Legacy DB]
```

**Fase E-F:** Roadmap incremental
- **Sprint 1-2:** Crear API facade sobre legacy (sin cambiar nada)
- **Sprint 3-4:** Extraer primera capacidad (ej: autenticación)
- **Sprint 5-6:** Routing: 10% tráfico a nuevo, 90% a legacy
- **Sprint 7-8:** Routing: 50/50, validar estabilidad
- **Sprint 9-10:** Routing: 100% a nuevo
- **Sprint 11:** Eliminar código legacy de esa capacidad
- Repetir para cada capacidad

**Consideraciones de Datos:**
- **Opción 1 - Dual Write:** Escribir en ambas DBs temporalmente
- **Opción 2 - Data Replication:** CDC del legacy a nuevo
- **Opción 3 - API de Datos:** Nuevo sistema lee legacy DB via APIs
- **Opción 4 - Event Sourcing:** Eventos como source of truth

---

## Expansión Internacional

### Contexto
Empresa que opera en un país y expande a múltiples geografías.

### Consideraciones Arquitecturales

**Fase A - Drivers:**
- Cumplir regulaciones locales (data residency, compliance)
- Baja latencia para usuarios en cada región
- Soporte multi-idioma, multi-moneda, multi-timezone
- Resiliencia ante fallas regionales

**Fase B - Negocio:**
- **Capacidades localizadas vs globales:**
  - Global: Catálogo de productos, pricing engine
  - Local: KYC (varía por país), payment methods, customer support

- **Procesos adaptables:**
  - Workflows configurables por país
  - Reglas de negocio externalizadas

**Fase D - Tecnología:**
- **Multi-region architecture:**
  - **Activo-Activo:** Usuarios en cada región usan región más cercana
  - **Activo-Pasivo:** Una región primaria, otras en standby

- **Data residency:**
  - Datos de clientes EU en EU (GDPR)
  - Datos de clientes en países con regulación local almacenados localmente
  - Datos globales (catálogo) replicados

- **Latencia:**
  - CDN global para assets estáticos
  - API Gateway en cada región
  - DB read replicas en cada región
  - Cache local

**Ejemplo AWS Multi-Region:**
```
Region: US-East-1 (primary)
- Full stack
- Master DB (writes)

Region: EU-West-1
- Full stack
- Read Replica + cache (reads)
- Algunos servicios locales (ej: KYC provider europeo)

Region: AP-Southeast-1
- Full stack
- Read Replica + cache

Data Flow:
- Writes: Siempre a US-East-1 (master)
- Reads: De replica local
- Cross-region replication: Async (eventual consistency)
```

**Desafíos:**
- **Consistency:** Elegir entre consistencia fuerte vs eventual (según caso de uso)
- **Conflictos:** Manejar writes concurrentes en multi-activo (CRDT, conflict resolution)
- **Testing:** Probar fallas de región, latencia inter-region
- **Complejidad:** Debugging distribuido, observabilidad multi-region

---

## Fusión y Adquisición (M&A)

### Contexto
Dos organizaciones se fusionan o una adquiere otra, necesitan integrar arquitecturas.

### Patrón de Aplicación ADM

**Fase A - Assessment rápido:**
- Inventariar sistemas de ambas organizaciones
- Identificar duplicaciones y gaps
- Definir estrategia de integración (absorber, coexistir, best-of-breed)

**Fase B-C - Análisis comparativo:**
| Capacidad          | Empresa A          | Empresa B          | Decisión TO-BE       |
|--------------------|--------------------|--------------------|----------------------|
| CRM                | Salesforce         | HubSpot            | Salesforce (más robusto) |
| ERP                | SAP                | Oracle             | SAP (keep A)         |
| E-commerce         | Custom             | Shopify            | Shopify (mejor)      |
| Data Warehouse     | Snowflake          | Redshift           | Snowflake (keep A)   |

**Estrategias de Integración:**

**1. Absorción (Empresa A absorbe B):**
- Migrar todos los sistemas de B a plataformas de A
- Descomisionar sistemas de B
- Típico cuando A es mucho más grande o tiene tecnología superior

**2. Best-of-Breed:**
- Elegir mejores sistemas de cada empresa
- Ambas empresas migran a selección "ganadora"
- Requiere disciplina y no caer en "todo es crítico"

**3. Coexistencia:**
- Mantener ambos stacks pero integrarlos
- Solo para transición temporal (no sostenible largo plazo)
- Requiere capa de integración robusta

**Fase D - Capa de Integración:**
```
[Sistemas Empresa A] ←→ [Integration Layer] ←→ [Sistemas Empresa B]
                              ↓
                      [Master Data Management]
                      [Single Source of Truth]
```

- APIs para integración
- MDM para entidades maestras (cliente, producto, empleado)
- Event bus para eventos de negocio

**Fase E-F - Roadmap:**
- **Day 1:** Coexistencia básica (pueden operar ambas empresas)
- **Months 1-6:** Integración de datos críticos (clientes, finanzas)
- **Months 7-12:** Consolidación de aplicaciones
- **Months 13-24:** Descomisionar sistemas redundantes

**Riesgos:**
- Disrupción de operación durante integración
- Pérdida de empleados clave (incertidumbre)
- Culturas tecnológicas incompatibles
- Contractos de vendors (licencias, no transferibles)
- Data quality y mapping entre sistemas incompatibles
