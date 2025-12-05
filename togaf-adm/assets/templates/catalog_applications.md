# Catálogo de Aplicaciones

**Proyecto:** [Nombre del proyecto]
**Fecha:** [Fecha]
**Versión:** [Versión]

## Propósito
Inventariar todas las aplicaciones de software, tanto actuales (AS-IS) como futuras (TO-BE), que soportan las capacidades de negocio.

---

## Inventario de Aplicaciones

| ID | Aplicación | Tipo | Vendor | Versión | Estado | Criticidad | Usuarios | Costo Anual |
|----|------------|------|--------|---------|--------|------------|----------|-------------|
| APP-001 | [Nombre] | [Tipo] | [Vendor] | [X.Y] | AS-IS/TO-BE/DEPRECAR | Alta/Media/Baja | [#] | [$] |
|  |  |  |  |  |  |  |  |  |

### Tipos de Aplicaciones
- **Custom:** Desarrollo in-house
- **COTS:** Commercial Off-The-Shelf (software comercial)
- **SaaS:** Software as a Service
- **Open Source:** Software de código abierto
- **Hybrid:** Combinación de los anteriores

### Estados
- **AS-IS:** Aplicación actual en uso
- **TO-BE:** Aplicación planificada/futura
- **DEPRECAR:** Aplicación a eliminar
- **MIGRAR:** Aplicación en transición
- **MODERNIZAR:** Aplicación a actualizar

---

## Detalle por Aplicación

### APP-001: [Nombre de la Aplicación]

**Información General:**
- **Nombre completo:** [Nombre]
- **Alias/Acrónimo:** [Alias]
- **Tipo:** ☐ Custom  ☐ COTS  ☐ SaaS  ☐ Open Source  ☐ Hybrid
- **Vendor/Proveedor:** [Nombre]
- **Versión actual:** [X.Y.Z]
- **Estado:** ☐ AS-IS  ☐ TO-BE  ☐ DEPRECAR  ☐ MIGRAR

**Propósito y Funcionalidad:**
[Descripción de qué hace la aplicación y por qué existe]

**Capacidades de Negocio que Soporta:**
- [CAP-001]: [Nombre capacidad]
- [CAP-002]: [Nombre capacidad]

**Criticidad:** ☐ Crítica  ☐ Alta  ☐ Media  ☐ Baja

**Usuarios:**
- **Número de usuarios:** [#]
- **Tipo de usuarios:** [Internos/Externos/Ambos]
- **Roles principales:** [Listar roles]

**Stack Tecnológico:**
- **Lenguaje/Framework:** [Tecnología]
- **Base de datos:** [DB]
- **Infraestructura:** [Cloud/On-prem/Hybrid]
- **Integraciones:** [Lista de aplicaciones con las que se integra]

**Propietario:**
- **Business Owner:** [Nombre y rol]
- **Technical Owner:** [Nombre y rol]
- **Equipo de soporte:** [Equipo]

**Costos:**
- **Licencias:** $[X]/año
- **Infraestructura:** $[Y]/año
- **Mantenimiento:** $[Z]/año
- **Total:** $[Total]/año

**Contratos:**
- **Fecha inicio:** [Fecha]
- **Fecha vencimiento:** [Fecha]
- **Términos de renovación:** [Detalles]
- **Exit clauses:** [Detalles]

**Métricas:**
| Métrica | Valor Actual | Objetivo | Observaciones |
|---------|--------------|----------|---------------|
| Disponibilidad (uptime) | [%] | [%] | |
| Performance (latency) | [ms] | [ms] | |
| Usuarios activos/mes | [#] | [#] | |
| Incidentes/mes | [#] | [#] | |

**Estado de Salud:**
- **Salud técnica:** ☐ Buena  ☐ Aceptable  ☐ Pobre  ☐ Crítica
- **Deuda técnica:** ☐ Baja  ☐ Media  ☐ Alta  ☐ Crítica
- **Satisfacción de usuarios:** [1-5 ⭐]

**Problemas/Pain Points Actuales:**
- [Problema 1]
- [Problema 2]
- [Problema 3]

**Decisión Arquitectural (para TO-BE):**
- ☐ **Keep:** Mantener sin cambios
- ☐ **Upgrade:** Actualizar versión/features
- ☐ **Replace:** Reemplazar por otra solución
- ☐ **Retire:** Eliminar (ya no necesaria)
- ☐ **Consolidate:** Consolidar con otra aplicación

**Rationale de la decisión:**
[Explicar por qué se tomó esta decisión]

**Plan de Acción:**
[Describir los siguientes pasos]

**Riesgos:**
- [Riesgo 1 y mitigación]
- [Riesgo 2 y mitigación]

**Dependencias:**
- **Depende de (upstream):** [APP-XXX, APP-YYY]
- **Es usado por (downstream):** [APP-ZZZ]

**Integraciones:**
| Aplicación Destino | Tipo Integración | Protocolo | Frecuencia | Criticidad | Observaciones |
|--------------------|------------------|-----------|------------|------------|---------------|
| [APP-XXX] | API REST | HTTPS | Real-time | Alta | |
| [APP-YYY] | Batch ETL | SFTP | Diario | Media | |

**Datos Gestionados:**
- **Entidades principales:** [Cliente, Pedido, etc.]
- **Volumen de datos:** [GB/TB]
- **Sensibilidad:** ☐ PII  ☐ Financiero  ☐ Confidencial  ☐ Público

---

### APP-002: [Nombre de la Aplicación]

[Repetir estructura anterior]

---

## Matrices de Análisis

### Matriz Aplicación - Capacidad

| Aplicación | CAP-001 | CAP-002 | CAP-003 | CAP-004 | CAP-005 |
|------------|---------|---------|---------|---------|---------|
| APP-001    | ✓       | ✓       |         |         | ✓       |
| APP-002    |         | ✓       | ✓       | ✓       |         |
| APP-003    | ✓       |         |         | ✓       | ✓       |

**Análisis:**
- Capacidades sin cobertura: [Lista]
- Aplicaciones con cobertura redundante: [Lista]

---

### Matriz Aplicación - Datos

Indica si la aplicación Crea (C), Lee (R), Actualiza (U) o Elimina (D) cada entidad de datos.

| Aplicación | Cliente | Pedido | Producto | Transacción | Inventario |
|------------|---------|--------|----------|-------------|------------|
| APP-001    | CRUD    | CR     | R        |             |            |
| APP-002    | R       | CRUD   | R        | CRUD        |            |
| APP-003    | R       | R      | CRUD     |             | CRUD       |

**Análisis:**
- **Data Ownership:** Identificar qué app es el "master" de cada entidad
- **Conflictos:** Detectar múltiples apps con permisos de escritura (requiere coordinación)

---

### Matriz de Integración

| De \ A | APP-001 | APP-002 | APP-003 | APP-004 |
|--------|---------|---------|---------|---------|
| APP-001| -       | API     | Event   |         |
| APP-002| API     | -       | Batch   | API     |
| APP-003|         | Event   | -       | API     |
| APP-004|         | API     |         | -       |

**Leyenda:**
- API: Integración síncrona (REST/GraphQL)
- Event: Integración asíncrona (eventos)
- Batch: Integración por lotes (ETL)
- DB: Acceso directo a base de datos (anti-patrón)

---

## Análisis de Portfolio

### Por Criticidad

| Criticidad | Cantidad | % del Total | Costo Anual Total |
|------------|----------|-------------|-------------------|
| Crítica    | [#]      | [%]         | $[X]              |
| Alta       | [#]      | [%]         | $[Y]              |
| Media      | [#]      | [%]         | $[Z]              |
| Baja       | [#]      | [%]         | $[W]              |
| **Total**  | [#]      | 100%        | $[Total]          |

### Por Tipo

| Tipo | Cantidad | % | Costo |
|------|----------|---|-------|
| Custom | [#] | [%] | $[X] |
| COTS | [#] | [%] | $[Y] |
| SaaS | [#] | [%] | $[Z] |
| Open Source | [#] | [%] | $[W] |

### Por Estado

| Estado | Cantidad | Plan |
|--------|----------|------|
| Keep | [#] | Mantener |
| Upgrade | [#] | Actualizar en [Timeline] |
| Replace | [#] | Reemplazar por [Solución] en [Timeline] |
| Retire | [#] | Eliminar en [Timeline] |
| Migrate | [#] | Migrar a [Destino] en [Timeline] |

---

## Roadmap de Aplicaciones

### Transiciones Planeadas

```
Q1 2025              Q2 2025              Q3 2025              Q4 2025
│                    │                    │                    │
├─ APP-001: Upgrade  │                    │                    │
│  (v2.0 → v3.0)     │                    │                    │
│                    ├─ APP-002: Replace  │                    │
│                    │  (Legacy → NewApp) │                    │
│                    │                    ├─ APP-003: Retire   │
│                    │                    │  (Decomission)     │
│                    │                    │                    ├─ APP-004: Migrate
│                    │                    │                    │  (On-prem → Cloud)
```

---

## Riesgos del Portfolio

| Riesgo | Aplicaciones Afectadas | Probabilidad | Impacto | Mitigación |
|--------|------------------------|--------------|---------|------------|
| [Riesgo 1] | [APP-XXX] | Alta/Media/Baja | Alto/Medio/Bajo | [Plan] |
|        |            |          |         |            |

**Ejemplos de riesgos:**
- Dependencia en aplicación legacy sin soporte
- Contrato de licencia venciendo
- Aplicación con deuda técnica crítica
- Vendor único sin alternativas
- Performance degradándose

---

## Oportunidades de Consolidación

| Aplicaciones Candidatas | Funcionalidad Overlap | Oportunidad | Ahorro Estimado |
|-------------------------|----------------------|-------------|-----------------|
| [APP-X, APP-Y] | [80% overlap] | Consolidar en APP-X | $[Z]/año |
|                |               |             |                 |

---

## Notas

[Agregar cualquier observación relevante sobre el portfolio de aplicaciones]
