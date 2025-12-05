# Cadena de Valor, Flujo de Valor y Mapa de Capacidades en TOGAF

## Propósito

Este documento define tres conceptos críticos para el análisis de arquitectura empresarial en TOGAF, explicando cuándo y cómo utilizarlos durante las fases ADM.

---

## 1. Cadena de Valor (Value Chain)

### Definición

La **Cadena de Valor** representa las actividades primarias y de soporte que una organización ejecuta para crear y entregar valor a sus clientes. Basado en el modelo de Michael Porter, muestra el flujo secuencial de actividades que transforman inputs en outputs valiosos.

### Cuándo Usar en ADM

- **Phase A (Architecture Vision):** Para identificar actividades clave que generan valor
- **Phase B (Business Architecture):** Para mapear capacidades a actividades de valor
- **Phase E (Opportunities and Solutions):** Para priorizar inversiones en actividades de alto impacto

### Componentes

**Actividades Primarias** (flujo directo de valor al cliente):
1. **Logística de Entrada:** Recepción, almacenamiento, gestión de inventario
2. **Operaciones:** Transformación de inputs en productos/servicios
3. **Logística de Salida:** Distribución de productos al cliente
4. **Marketing y Ventas:** Promoción y venta de productos/servicios
5. **Servicio Post-Venta:** Soporte, mantenimiento, garantías

**Actividades de Soporte** (habilitan las primarias):
1. **Infraestructura de la Empresa:** Gestión general, finanzas, legal
2. **Gestión de RRHH:** Reclutamiento, capacitación, desarrollo
3. **Desarrollo Tecnológico:** I+D, innovación, mejora de procesos
4. **Adquisiciones:** Compra de materiales, servicios, tecnología

### Estructura del Diagrama

```
┌─────────────────────────────────────────────────────────────┐
│         ACTIVIDADES DE SOPORTE (Margin)                     │
├─────────────────────────────────────────────────────────────┤
│ Infraestructura | Gestión RRHH | Tecnología | Adquisiciones│
└─────────────────────────────────────────────────────────────┘
        ↓                ↓              ↓            ↓
┌─────────┬──────────┬──────────┬──────────┬─────────────────┐
│Logística│          │Logística │Marketing │                 │
│Entrada  │Operacion.│  Salida  │  Ventas  │ Servicio        │
└─────────┴──────────┴──────────┴──────────┴─────────────────┘
   →         →          →          →           →    (MARGEN)
```

### Ejemplo: Fintech Lending

**Actividades Primarias:**
- Logística Entrada: Captación de leads (digital), recopilación de datos
- Operaciones: Scoring crediticio, underwriting, desembolso
- Logística Salida: Transferencia de fondos, entrega de contrato
- Marketing/Ventas: Campañas digitales, onboarding digital
- Servicio: Atención al cliente, gestión de pagos, cobranzas

**Actividades Soporte:**
- Infraestructura: Compliance, finanzas, legal
- RRHH: Reclutamiento de data scientists, capacitación en riesgo
- Tecnología: ML para scoring, plataforma cloud, APIs
- Adquisiciones: Proveedores de datos (bureaus), cloud (AWS), KYC/AML

---

## 2. Flujo de Valor (Value Stream)

### Definición

El **Flujo de Valor** (Value Stream) representa el flujo end-to-end de actividades, información y materiales necesarios para entregar un producto o servicio específico al cliente, desde el request inicial hasta la entrega de valor.

A diferencia de la cadena de valor (vista organizacional genérica), un flujo de valor es específico para un producto/servicio particular y cruza múltiples departamentos y sistemas.

### Cuándo Usar en ADM

- **Phase B (Business Architecture):** Para entender procesos cross-funcionales
- **Phase C (Information Systems):** Para identificar flujos de datos críticos
- **Phase E (Opportunities and Solutions):** Para detectar cuellos de botella y optimizaciones
- **Phase F (Migration Planning):** Para diseñar la transformación por flujos de valor

### Características Clave

- **End-to-end:** Desde trigger inicial hasta entrega de valor
- **Customer-centric:** Centrado en la experiencia del cliente
- **Cross-funcional:** Atraviesa departamentos y sistemas
- **Medible:** Incluye métricas de tiempo, calidad, costo

### Componentes de un Value Stream

1. **Trigger:** Evento que inicia el flujo (ej: solicitud de crédito)
2. **Stages:** Etapas del flujo (ej: Solicitud → Evaluación → Aprobación → Desembolso)
3. **Activities:** Actividades en cada etapa
4. **Stakeholders:** Personas/sistemas involucrados en cada etapa
5. **Information Flow:** Datos que fluyen entre etapas
6. **Metrics:** Lead time, cycle time, % automatización, error rate

### Estructura del Diagrama

```
Trigger → [Stage 1] → [Stage 2] → [Stage 3] → Value Delivered
            ↓            ↓            ↓
         Activities   Activities   Activities
            ↓            ↓            ↓
        Stakeholders Stakeholders Stakeholders
            ↓            ↓            ↓
          Systems     Systems      Systems
```

### Ejemplo: Value Stream "Originación de Crédito" (Fintech)

**Trigger:** Cliente solicita crédito online

**Stages:**
1. **Solicitud y Captura de Datos**
   - Activities: Registro, validación de identidad (KYC), recopilación de docs
   - Stakeholders: Cliente, Bot de onboarding
   - Systems: Portal Web, API KYC, Document Storage
   - Metrics: Tiempo promedio 5 min, 85% completitud

2. **Evaluación Crediticia**
   - Activities: Pull credit bureau, ML scoring, validación de ingresos
   - Stakeholders: Motor de scoring (automático), Analista de riesgo (casos edge)
   - Systems: Score Engine, Bureau APIs, Rules Engine
   - Metrics: 90% automatizado, score en 30 seg

3. **Aprobación y Pricing**
   - Activities: Decisión (aprobado/rechazado), cálculo de tasa, generación de oferta
   - Stakeholders: Motor de decisión (automático), Oficial de crédito (manual review)
   - Systems: Decision Engine, Pricing Engine, Offer Generator
   - Metrics: 95% automático, 2 min promedio

4. **Formalización y Desembolso**
   - Activities: Firma digital de contrato, programación de desembolso, transferencia
   - Stakeholders: Cliente, Sistema de pagos
   - Systems: e-Signature API, Core Banking, Payment Gateway
   - Metrics: 3 min promedio, 99.9% éxito en transferencia

**Value Delivered:** Crédito aprobado y desembolsado en cuenta del cliente

**Métricas End-to-End:**
- Lead Time: 15 minutos (solicitud → desembolso)
- Cycle Time: 10 minutos (tiempo activo de procesamiento)
- Automation Rate: 92%
- Approval Rate: 68%
- Error Rate: 0.5%

### Value Stream Mapping (VSM)

El VSM es una herramienta para visualizar el flujo de valor actual (AS-IS) y diseñar el estado futuro (TO-BE), identificando:

- **Value-adding activities:** Actividades que el cliente paga
- **Non-value-adding but necessary:** Ej: compliance, controles
- **Waste:** Retrabajos, esperas, handoffs innecesarios

**En TOGAF ADM:**
- Usar VSM en Phase B para baseline actual
- Usar VSM en Phase E para diseñar estado futuro optimizado
- Identificar gaps de automatización, integración, capacidades

---

## 3. Mapa de Capacidades (Capability Map)

### Definición

El **Mapa de Capacidades** es una representación visual y estructurada de las capacidades de negocio que una organización necesita para ejecutar su estrategia, organizadas jerárquicamente y categorizadas por dominios.

Una capacidad es "lo que hace el negocio" (ej: "Gestionar Clientes"), independiente de cómo lo hace (procesos, aplicaciones, personas).

### Cuándo Usar en ADM

- **Phase A (Architecture Vision):** Mapa de capacidades de alto nivel (Nivel 1-2)
- **Phase B (Business Architecture):** Mapa de capacidades detallado (Nivel 3-4) con análisis de madurez
- **Phase E (Opportunities and Solutions):** Para priorizar inversiones en capacidades críticas

### Niveles de Detalle

**Nivel 1 - Dominios de Capacidad:**
Categorías amplias (4-8 dominios típicamente)

Ejemplo: Gestión de Clientes | Gestión de Productos | Gestión de Operaciones | Gestión de Riesgo

**Nivel 2 - Capacidades Principales:**
Descomposición de dominios (3-6 capacidades por dominio)

Ejemplo (Gestión de Clientes):
- Adquisición de Clientes
- Onboarding de Clientes
- Servicio al Cliente
- Retención de Clientes

**Nivel 3 - Sub-capacidades:**
Descomposición detallada (2-5 sub-capacidades)

Ejemplo (Onboarding de Clientes):
- Verificación de Identidad (KYC)
- Verificación de Ingresos
- Apertura de Cuenta
- Configuración de Productos

**Nivel 4 - Capacidades Atómicas:**
Nivel más granular (usado solo cuando necesario)

### Estructura del Diagrama

```
┌─────────────────────────────────────────────────────────────┐
│                    NIVEL 1: DOMINIOS                        │
├────────────┬────────────┬────────────┬────────────┬─────────┤
│ Gestión    │ Gestión    │ Gestión    │ Gestión    │ Gestión │
│ Clientes   │ Productos  │ Operaciones│ Riesgo     │ Soporte │
└────────────┴────────────┴────────────┴────────────┴─────────┘
      │
┌─────┴───────────────────────────────────────────────────────┐
│           NIVEL 2: CAPACIDADES PRINCIPALES                  │
├─────────────┬─────────────┬─────────────┬──────────────────┤
│ Adquisición │ Onboarding  │ Servicio    │ Retención        │
│ Clientes    │ Clientes    │ Cliente     │ Clientes         │
└─────────────┴─────────────┴─────────────┴──────────────────┘
                    │
┌───────────────────┴─────────────────────────────────────────┐
│              NIVEL 3: SUB-CAPACIDADES                       │
├────────────┬────────────┬────────────┬────────────────────┤
│ KYC        │ Verificac. │ Apertura   │ Config.            │
│            │ Ingresos   │ Cuenta     │ Productos          │
└────────────┴────────────┴────────────┴────────────────────┘
```

### Atributos de una Capacidad

Para cada capacidad, documentar:

1. **ID y Nombre:** Identificador único y nombre descriptivo
2. **Descripción:** Qué hace la capacidad (no cómo)
3. **Nivel Jerárquico:** 1, 2, 3, o 4
4. **Dominio Padre:** A qué dominio pertenece
5. **Propietario:** Quién es responsable de la capacidad en el negocio
6. **Criticidad:** Crítica / Alta / Media / Baja
7. **Madurez AS-IS:** Nivel actual (0-5 según escala CMMI)
8. **Madurez TO-BE:** Nivel objetivo
9. **Gap:** Diferencia entre TO-BE y AS-IS
10. **Procesos Habilitados:** Qué procesos dependen de esta capacidad
11. **Aplicaciones que Soportan:** Sistemas que implementan la capacidad
12. **Métricas:** KPIs clave para medir efectividad

### Ejemplo: Mapa de Capacidades Fintech (Nivel 1-2)

```
┌──────────────────────────────────────────────────────────────────┐
│                    MAPA DE CAPACIDADES                           │
├──────────┬──────────┬──────────┬──────────┬──────────┬──────────┤
│ Gestión  │ Gestión  │ Gestión  │ Gestión  │ Gestión  │ Gestión  │
│ Clientes │ Productos│ Crédito  │ Riesgo   │ Finanzas │ Tecnolog.│
└──────────┴──────────┴──────────┴──────────┴──────────┴──────────┘

Gestión de Clientes:
├─ Adquisición de Clientes (Marketing, Campañas)
├─ Onboarding de Clientes (KYC, Verificación)
├─ Servicio al Cliente (Soporte, Consultas)
└─ Retención de Clientes (Loyalty, Upsell)

Gestión de Productos:
├─ Diseño de Productos (Innovación, Pricing)
├─ Catálogo de Productos (Gestión de ofertas)
└─ Lifecycle de Productos (Lanzamiento, Deprecación)

Gestión de Crédito:
├─ Originación de Crédito (Solicitud, Scoring, Aprobación)
├─ Desembolso (Transferencia de fondos)
├─ Servicing de Crédito (Pagos, Estados de cuenta)
└─ Cobranzas (Recordatorios, Gestión de mora)

Gestión de Riesgo:
├─ Riesgo de Crédito (Scoring, Modelos, Políticas)
├─ Riesgo Operacional (Controles, Auditoría)
├─ Fraude y AML (Detección, Prevención)
└─ Compliance (Regulatorio, Reportes)

Gestión Financiera:
├─ Contabilidad (GL, Reconciliación)
├─ Tesorería (Cash management, Inversiones)
├─ Reporting Financiero (Estados financieros, Dashboard)
└─ Planning & Analysis (Presupuestos, Forecast)

Gestión de Tecnología:
├─ Desarrollo de Software (Build, Deploy, CI/CD)
├─ Infraestructura (Cloud, Redes, Seguridad)
├─ Data & Analytics (DWH, BI, ML)
└─ Integración (APIs, Middleware, Batch)
```

### Análisis de Madurez en Capability Map

Visualizar la madurez de capacidades es crítico para priorizar inversiones.

**Escala de Madurez (CMMI-style):**

- **Nivel 0:** No existe la capacidad
- **Nivel 1:** Ad-hoc, manual, dependiente de individuos
- **Nivel 2:** Repetible manualmente con procedimientos básicos
- **Nivel 3:** Definido, documentado, estandarizado
- **Nivel 4:** Gestionado con métricas, monitoreo continuo
- **Nivel 5:** Optimizado, automatizado, mejora continua

**Visualización con Mapa de Calor:**

```
Capacidad                 │ AS-IS │ TO-BE │ Gap │ Criticidad │
──────────────────────────┼───────┼───────┼─────┼────────────┤
Onboarding Clientes       │   2   │   4   │ +2  │   ALTA     │ 🔴
Scoring Crediticio        │   1   │   5   │ +4  │  CRÍTICA   │ 🔴
Desembolso                │   3   │   4   │ +1  │   ALTA     │ 🟡
Servicio Cliente          │   2   │   3   │ +1  │   MEDIA    │ 🟢
Fraud Detection           │   0   │   3   │ +3  │   ALTA     │ 🔴
Reporting Financiero      │   4   │   4   │  0  │   MEDIA    │ 🟢

🔴 = Gap crítico (gap >= 2 o criticidad alta con gap > 0)
🟡 = Gap moderado
🟢 = Gap bajo o sin gap
```

---

## 4. Relación Entre los Tres Conceptos

### Cómo se Complementan

| Concepto | Pregunta que Responde | Vista | Uso en TOGAF |
|----------|----------------------|-------|--------------|
| **Cadena de Valor** | ¿Cómo generamos valor organizacionalmente? | Organizacional, estratégica | Phase A (visión), Phase B (contexto) |
| **Flujo de Valor** | ¿Cómo entregamos valor al cliente end-to-end? | Operacional, por producto/servicio | Phase B (procesos), Phase C (datos/apps), Phase E (optimización) |
| **Mapa de Capacidades** | ¿Qué capacidades necesitamos para operar? | Estructural, independiente de cómo | Phase A (alto nivel), Phase B (detallado), Phase E (priorización) |

### Ejemplo Integrado: Fintech

**Cadena de Valor:**
- Actividades primarias: Captación → Scoring → Underwriting → Desembolso → Servicing
- Actividades soporte: Compliance, Tech, RRHH

**Flujo de Valor: "Originación de Crédito"**
- Trigger: Solicitud de crédito
- Stages: Solicitud → Evaluación → Aprobación → Desembolso
- End-to-end: 15 minutos, 92% automatizado

**Mapa de Capacidades:**
- Dominio: Gestión de Crédito
  - Capacidad: Originación de Crédito (Nivel 2)
    - Sub-capacidades: KYC, Scoring, Decisión, Pricing (Nivel 3)
  - Madurez AS-IS: Nivel 2 (manual scoring)
  - Madurez TO-BE: Nivel 5 (ML scoring automatizado)

**Relación:**
- La **Cadena de Valor** identifica que "Operaciones" (scoring/underwriting) es actividad primaria crítica
- El **Flujo de Valor** mapea cómo ejecutamos end-to-end la originación (desde solicitud hasta desembolso)
- El **Mapa de Capacidades** define que necesitamos capacidades de "Scoring Crediticio" y "Decisión Automatizada" para ejecutar el flujo
- El análisis revela: gap de madurez en Scoring (Nivel 1 → 5) es crítico para optimizar el flujo de valor

---

## 5. Cuándo Usar Cada Uno en ADM

### Phase A: Architecture Vision

**Cadena de Valor:**
- ✅ Usar para: Identificar actividades clave que generan valor
- Output: Diagrama de cadena de valor de alto nivel

**Flujo de Valor:**
- ⚠️ Opcional: Solo mencionar flujos críticos
- Output: Lista de flujos de valor principales

**Mapa de Capacidades:**
- ✅ Usar para: Mapa de capacidades Nivel 1-2 (alto nivel)
- Output: Dominios y capacidades principales

### Phase B: Business Architecture

**Cadena de Valor:**
- ⚠️ Referencia: Como contexto para mapear procesos
- Output: Mapeo de procesos a cadena de valor

**Flujo de Valor:**
- ✅ Usar para: Modelar flujos end-to-end críticos
- Output: 3-5 flujos de valor detallados (AS-IS y TO-BE)

**Mapa de Capacidades:**
- ✅ Usar para: Mapa de capacidades Nivel 3 detallado con análisis de madurez
- Output: Capability map completo + gap analysis

### Phase C: Information Systems

**Flujo de Valor:**
- ✅ Usar para: Identificar flujos de datos críticos en cada value stream
- Output: Data flow diagrams por value stream

**Mapa de Capacidades:**
- ✅ Usar para: Mapeo de aplicaciones a capacidades (Application-Capability Matrix)
- Output: Matriz que muestra qué aplicaciones soportan cada capacidad

### Phase E: Opportunities and Solutions

**Cadena de Valor:**
- ✅ Usar para: Priorizar inversiones en actividades de alto valor
- Output: Análisis de impacto por actividad de valor

**Flujo de Valor:**
- ✅ Usar para: Identificar cuellos de botella y optimizaciones
- Output: VSM con análisis de waste, lead time, automation opportunities

**Mapa de Capacidades:**
- ✅ Usar para: Priorizar work packages por gaps de capacidad críticos
- Output: Roadmap de capacidades (qué capacidades mejorar en cada release)

### Phase F: Migration Planning

**Flujo de Valor:**
- ✅ Usar para: Diseñar transformación por flujos de valor (ej: migrar flujo por flujo)
- Output: Migration roadmap organizado por value streams

**Mapa de Capacidades:**
- ✅ Usar para: Secuenciar mejoras de capacidades con dependencias
- Output: Dependency map de capacidades

---

## 6. Mejores Prácticas

### Para Cadena de Valor

1. **Adaptar a la industria:** No todas las empresas tienen las mismas actividades primarias
   - Retail: Aprovisionamiento → Merchandising → Venta → Post-venta
   - SaaS: Desarrollo → Marketing → Venta → Onboarding → Support
   - Fintech: Captación → Scoring → Underwriting → Servicing

2. **Enfocarse en diferenciadores:** Identificar qué actividades generan ventaja competitiva
   - Ej: En fintech, "Scoring Crediticio ML" es diferenciador vs competencia manual

3. **No sobre-detallar:** La cadena de valor es estratégica, no operacional

### Para Flujo de Valor

1. **Seleccionar flujos críticos:** No modelar todos los flujos, solo los 3-5 más importantes
   - Criterios: Volumen, impacto cliente, generación de ingresos, costo operativo

2. **Medir métricas end-to-end:**
   - Lead Time (tiempo total de inicio a fin)
   - Cycle Time (tiempo de procesamiento activo)
   - % Automation
   - Error rate / Rework rate
   - Customer satisfaction

3. **Usar VSM para detectar waste:**
   - Esperas innecesarias (ej: aprobaciones manuales que pueden automatizarse)
   - Handoffs excesivos (ej: 5 sistemas diferentes para un flujo)
   - Retrabajos (ej: errores de validación que requieren re-ingresar datos)

4. **Diseñar TO-BE basado en principios Lean:**
   - Eliminar waste
   - Reducir handoffs
   - Automatizar actividades repetitivas
   - Mejorar visibilidad (tracking del flujo)

### Para Mapa de Capacidades

1. **Mantener independencia de implementación:**
   - ❌ Mal: "Capacidad de usar Salesforce" (específico a herramienta)
   - ✅ Bien: "Capacidad de Gestionar Relaciones con Clientes" (independiente de CRM)

2. **Usar verbos de negocio, no tecnológicos:**
   - ❌ Mal: "ETL de datos"
   - ✅ Bien: "Integración de Datos"

3. **Balancear niveles de detalle:**
   - No crear Nivel 4 si no es necesario (over-engineering)
   - Típicamente Nivel 3 es suficiente para la mayoría de proyectos

4. **Asignar ownership claro:**
   - Cada capacidad debe tener un business owner (no IT owner)

5. **Enfocarse en gaps críticos:**
   - Usar matriz de criticidad vs madurez
   - Priorizar capacidades: Alta criticidad + Baja madurez = URGENTE

6. **Evitar confundir capacidades con procesos:**
   - Capacidad: "Qué" hace el negocio (ej: "Evaluar Riesgo de Crédito")
   - Proceso: "Cómo" lo hace (ej: "Proceso de Scoring Crediticio con ML")

---

## 7. Templates y Scripts

Para generar diagramas visuales de estos conceptos, usar los scripts disponibles:

### Scripts Disponibles

**`scripts/generate_value_chain.py`**
- Genera diagrama Mermaid de cadena de valor
- Input: JSON con actividades primarias y de soporte
- Output: Diagrama Mermaid renderizable

**`scripts/generate_value_stream.py`**
- Genera diagrama Mermaid de flujo de valor
- Input: JSON con stages, activities, stakeholders, systems
- Output: Diagrama Mermaid tipo swimlane

**`scripts/generate_capability_map.py`**
- Genera diagrama Mermaid de mapa de capacidades
- Input: JSON con dominios, capacidades (nivel 1-3), madurez
- Output: Diagrama Mermaid con heat map de madurez

### Uso en ADM

Cuando el usuario solicite visualizar estos conceptos:

1. Recopilar información mediante preguntas
2. Ejecutar el script correspondiente
3. Presentar el diagrama Mermaid (se renderiza automáticamente en markdown)
4. Iterar basado en feedback del usuario

---

## Conclusión

- **Cadena de Valor:** Vista estratégica organizacional de cómo generamos valor
- **Flujo de Valor:** Vista operacional end-to-end de cómo entregamos valor por producto/servicio
- **Mapa de Capacidades:** Vista estructural de qué capacidades necesitamos independientemente del cómo

Estos tres conceptos son complementarios y esenciales para un análisis de arquitectura empresarial completo en TOGAF ADM.
