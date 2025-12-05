# Análisis de Brechas (Gap Analysis)

**Proyecto:** [Nombre del proyecto]
**Fecha:** [Fecha]
**Versión:** [Versión]

## Propósito
Identificar y documentar las diferencias (brechas) entre la arquitectura actual (AS-IS) y la arquitectura objetivo (TO-BE) en todas las dimensiones: negocio, datos, aplicaciones y tecnología.

---

## Resumen Ejecutivo

| Dimensión | # Brechas Totales | Críticas | Altas | Medias | Bajas |
|-----------|-------------------|----------|-------|--------|-------|
| Negocio | [#] | [#] | [#] | [#] | [#] |
| Datos | [#] | [#] | [#] | [#] | [#] |
| Aplicaciones | [#] | [#] | [#] | [#] | [#] |
| Tecnología | [#] | [#] | [#] | [#] | [#] |
| **TOTAL** | **[#]** | **[#]** | **[#]** | **[#]** | **[#]** |

---

## Metodología

### Tipos de Brechas

**1. Gap de Capacidad (Capability Gap):**
- Capacidad no existe en AS-IS pero se requiere en TO-BE
- **Acción:** Crear/Adquirir

**2. Gap de Madurez (Maturity Gap):**
- Capacidad existe pero no al nivel requerido
- **Acción:** Mejorar/Evolucionar

**3. Gap de Eliminación (Elimination Gap):**
- Elemento existe en AS-IS pero no en TO-BE
- **Acción:** Deprecar/Eliminar

**4. Gap de Transformación (Transformation Gap):**
- Elemento existe pero requiere cambio fundamental
- **Acción:** Reemplazar/Rediseñar

### Clasificación de Prioridad

- **CRÍTICO:** Bloqueador para objetivos de negocio, debe resolverse inmediatamente
- **ALTO:** Impacto significativo, resolver en próximos 3-6 meses
- **MEDIO:** Importante pero no urgente, resolver en 6-12 meses
- **BAJO:** Nice-to-have, resolver cuando haya capacidad

---

## Brechas de Negocio

### Brechas de Capacidades

| ID | Capacidad | Tipo de Gap | AS-IS | TO-BE | Impacto | Esfuerzo | Prioridad | Owner |
|----|-----------|-------------|-------|-------|---------|----------|-----------|-------|
| BG-001 | [Nombre] | Capacidad Nueva | No existe | Nivel 4 | Alto | Alto | CRÍTICO | [Owner] |
| BG-002 | [Nombre] | Madurez | Nivel 2 | Nivel 4 | Alto | Medio | ALTO | [Owner] |
| BG-003 | [Nombre] | Eliminación | Nivel 3 | No requerida | Bajo | Bajo | BAJO | [Owner] |

### Detalle de Brecha BG-001

**Capacidad:** [Nombre de la capacidad]

**Tipo de Gap:** ☐ Nueva  ☐ Madurez  ☐ Eliminación  ☐ Transformación

**Descripción:**
[Descripción detallada del gap]

**Estado AS-IS:**
[Cómo se ejecuta hoy, o "No existe"]

**Estado TO-BE:**
[Cómo debe ejecutarse en el futuro]

**Razón de Negocio:**
[Por qué es necesario cerrar este gap]

**Impacto de NO cerrar el gap:**
[Consecuencias de no actuar]

**Opciones para cerrar el gap:**
1. [Opción 1]: [Descripción, pros, contras, costo, tiempo]
2. [Opción 2]: [Descripción, pros, contras, costo, tiempo]
3. [Opción 3]: [Descripción, pros, contras, costo, tiempo]

**Opción Recomendada:** [#]

**Rationale:** [Por qué esta opción]

**Estimación:**
- **Esfuerzo:** [X meses-persona]
- **Costo:** $[Y]
- **Timeline:** [Z meses]

**Dependencias:**
- Requiere: [BG-XXX, AG-YYY]
- Habilita: [BG-ZZZ]

**Riesgos:**
| Riesgo | Probabilidad | Impacto | Mitigación |
|--------|--------------|---------|------------|
| [Riesgo 1] | Alta/Media/Baja | Alto/Medio/Bajo | [Plan] |

**Criterios de Éxito:**
- [Criterio 1]
- [Criterio 2]
- [Métrica de medición]

---

### Brechas de Procesos

| ID | Proceso | AS-IS | TO-BE | Gap | Impacto | Prioridad |
|----|---------|-------|-------|-----|---------|-----------|
| BP-001 | [Nombre] | Manual | Automatizado 90% | +90% automatización | Alto | CRÍTICO |
| BP-002 | [Nombre] | Tiempo: 5 días | Tiempo: 2 horas | -95% tiempo | Alto | ALTO |

---

## Brechas de Datos

### Brechas de Entidades de Datos

| ID | Entidad | Tipo de Gap | AS-IS | TO-BE | Impacto | Prioridad |
|----|---------|-------------|-------|-------|---------|-----------|
| DG-001 | [Entidad] | Nueva | No existe | Requerida | Alto | ALTO |
| DG-002 | [Entidad] | Transformación | Modelo relacional | Modelo evento | Medio | MEDIO |
| DG-003 | [Entidad] | Calidad | 60% completa | 95% completa | Alto | ALTO |

### Brechas de Calidad de Datos

| Entidad | Problema AS-IS | Target TO-BE | Gap | Acción |
|---------|----------------|--------------|-----|--------|
| Cliente | 40% registros incompletos | 95% completos | -55% | Data cleansing + validaciones |
| Producto | Duplicados (15%) | <1% duplicados | -14% | Deduplicación + MDM |
| Transacción | No auditabilidad | 100% auditable | Crítico | Event sourcing |

### Brechas de Gobierno de Datos

| Aspecto | AS-IS | TO-BE | Gap | Acción |
|---------|-------|-------|-----|--------|
| Data Ownership | Indefinido | Owner por entidad | Crítico | Definir + implementar gov model |
| Data Privacy | Manual | Automatizado (GDPR) | Alto | Implementar privacy framework |
| Data Lineage | No existe | Full lineage | Alto | Implementar data catalog |

---

## Brechas de Aplicaciones

### Brechas de Portfolio de Aplicaciones

| ID | Aplicación | Tipo de Gap | AS-IS | TO-BE | Acción | Prioridad |
|----|------------|-------------|-------|-------|--------|-----------|
| AG-001 | [App] | Nueva | No existe | Requerida | Build/Buy | CRÍTICO |
| AG-002 | [App] | Reemplazo | Legacy monolito | Microservicios | Refactor | ALTO |
| AG-003 | [App] | Eliminación | En uso | Deprecar | Retire | MEDIO |
| AG-004 | [App] | Modernización | v1.0 legacy | v3.0 modern | Upgrade | ALTO |

### Detalle de Build vs Buy

Para gaps que requieren nuevas aplicaciones:

| Gap ID | Aplicación Requerida | Opción Build | Opción Buy | Recomendación | Rationale |
|--------|---------------------|--------------|------------|---------------|-----------|
| AG-001 | [Nombre] | [$X, Y meses] | [Vendor, $Z, W meses] | Buy | [Razón] |

### Brechas de Integración

| ID | Integración | AS-IS | TO-BE | Gap | Impacto | Acción |
|----|-------------|-------|-------|-----|---------|--------|
| IG-001 | App A ↔ App B | No existe | API REST | Nueva | Alto | Implementar API |
| IG-002 | App C ↔ App D | DB directo | Event-driven | Transformación | Medio | Implementar events |
| IG-003 | App E ↔ App F | Batch diario | Real-time | Mejora | Alto | Implementar streaming |

---

## Brechas de Tecnología

### Brechas de Infraestructura

| ID | Componente | Tipo de Gap | AS-IS | TO-BE | Acción | Prioridad |
|----|------------|-------------|-------|-------|--------|-----------|
| TG-001 | Compute | Transformación | VMs on-prem | Containers cloud | Migrate | CRÍTICO |
| TG-002 | Database | Reemplazo | Oracle | PostgreSQL | Migrate | CRÍTICO |
| TG-003 | Networking | Nueva | No existe | API Gateway | Implement | ALTO |
| TG-004 | Observability | Mejora | Logs básicos | APM completo | Implement | MEDIO |

### Brechas de Skills/Competencias

| Tecnología TO-BE | Expertise Requerido | Expertise Actual | Gap | Acción |
|------------------|---------------------|------------------|-----|--------|
| Kubernetes | Alto | Bajo | -3 levels | Training + contratar 2 engineers |
| AWS | Alto | Medio | -1 level | Training + certificaciones |
| Terraform | Medio | Ninguno | Crítico | Training + contratar 1 engineer |
| React | Medio | Alto | OK | Mantener |

**Plan de Capacitación:**
| Tecnología | # Personas | Tipo Training | Costo | Timeline |
|------------|------------|---------------|-------|----------|
| Kubernetes | 5 | Curso + certificación | $10k | Q1 2025 |
| AWS | 10 | Curso online + labs | $15k | Q1-Q2 2025 |
| Terraform | 8 | Workshop interno | $5k | Q1 2025 |

---

## Consolidación de Brechas

### Brechas Críticas (Top 10)

Ordenadas por prioridad (considerando impacto × urgencia):

| Rank | ID | Brecha | Dimensión | Impacto | Esfuerzo | Plazo | Owner |
|------|----|----- ---|-----------|---------|----------|-------|-------|
| 1 | BG-001 | [Descripción] | Negocio | Alto | Alto | Q1 | [Owner] |
| 2 | AG-002 | [Descripción] | App | Alto | Alto | Q1-Q2 | [Owner] |
| 3 | TG-001 | [Descripción] | Tech | Alto | Medio | Q2 | [Owner] |
| 4 | DG-003 | [Descripción] | Datos | Alto | Bajo | Q2 | [Owner] |
| 5 | BG-002 | [Descripción] | Negocio | Medio | Alto | Q3 | [Owner] |

---

## Matriz de Impacto vs Esfuerzo

Visualización de brechas para priorización:

```
Alto    │ [BG-002]     │ [BG-001] ✓
Impacto │ [AG-004]     │ [AG-002] ✓
        │              │ [TG-001] ✓
        │ [TG-004]     │ [DG-003] ✓
Bajo    │ [BG-003]     │ [IG-001]
        └──────────────┴────────────
         Bajo Esfuerzo   Alto Esfuerzo

✓ = Prioridad ALTA (Quick wins o Strategic)
```

**Cuadrantes:**
- **Alto Impacto + Bajo Esfuerzo:** Quick wins - priorizar inmediatamente
- **Alto Impacto + Alto Esfuerzo:** Strategic - planear cuidadosamente
- **Bajo Impacto + Bajo Esfuerzo:** Fill-ins - hacer cuando haya capacidad
- **Bajo Impacto + Alto Esfuerzo:** Thankless tasks - evitar o re-evaluar

---

## Agrupación en Paquetes de Trabajo

### Paquete 1: [Nombre]

**Objetivo:** [Objetivo del paquete]

**Brechas incluidas:**
- BG-001: [Nombre]
- AG-002: [Nombre]
- TG-001: [Nombre]

**Rationale de agrupación:**
[Por qué estas brechas van juntas - dependencias, sinergia, etc.]

**Estimación consolidada:**
- **Esfuerzo:** [X meses-persona]
- **Costo:** $[Y]
- **Timeline:** [Z meses]

**Dependencias externas:**
- [Dependencia 1]
- [Dependencia 2]

**Riesgos del paquete:**
| Riesgo | Mitigación |
|--------|------------|
| [Riesgo 1] | [Plan] |

---

### Paquete 2: [Nombre]

[Repetir estructura]

---

## Roadmap de Cierre de Brechas

```
Q1 2025          Q2 2025          Q3 2025          Q4 2025
│                │                │                │
├─ Paquete 1     │                │                │
│  (5 brechas)   │                │                │
│                ├─ Paquete 2     │                │
│                │  (3 brechas)   │                │
│                │                ├─ Paquete 3     │
│                │                │  (4 brechas)   │
│                │                │                ├─ Paquete 4
│                │                │                │  (2 brechas)
│
Milestone 1      Milestone 2      Milestone 3      Milestone 4
(30% gaps)       (60% gaps)       (85% gaps)       (100% gaps)
```

---

## Métricas de Progreso

### KPIs de Cierre de Brechas

| Métrica | Baseline | Q1 Target | Q2 Target | Q3 Target | Q4 Target |
|---------|----------|-----------|-----------|-----------|-----------|
| % Brechas cerradas | 0% | 30% | 60% | 85% | 100% |
| % Brechas críticas cerradas | 0% | 60% | 100% | 100% | 100% |
| Inversión acumulada | $0 | $X | $Y | $Z | $Total |

### Tracking

| ID | Brecha | Prioridad | Estado | % Completado | ETA | Owner | Bloqueadores |
|----|--------|-----------|--------|--------------|-----|-------|--------------|
| BG-001 | [Nombre] | CRÍTICO | In Progress | 60% | Q1 | [Owner] | Ninguno |
| AG-002 | [Nombre] | ALTO | Planning | 10% | Q2 | [Owner] | Requiere BG-001 |

**Estados:**
- **Not Started:** No iniciado
- **Planning:** En planificación
- **In Progress:** En ejecución
- **Blocked:** Bloqueado
- **Completed:** Completado
- **Cancelled:** Cancelado

---

## Notas

[Observaciones adicionales sobre el análisis de brechas]
