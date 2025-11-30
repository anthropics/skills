# Matriz Proceso - Aplicación

**Proyecto:** [Nombre del proyecto]
**Fecha:** [Fecha]
**Versión:** [Versión]

## Propósito
Mapear qué aplicaciones soportan qué procesos de negocio, identificando gaps de cobertura y redundancias.

---

## Matriz Proceso - Aplicación

| Proceso / Aplicación | APP-001<br>[Nombre] | APP-002<br>[Nombre] | APP-003<br>[Nombre] | APP-004<br>[Nombre] | APP-005<br>[Nombre] | Cobertura |
|----------------------|---------------------|---------------------|---------------------|---------------------|---------------------|-----------|
| **PR-001:** [Proceso 1] | ✓ | ✓ | | | | 2 apps |
| **PR-002:** [Proceso 2] | ✓ | | ✓ | ✓ | | 3 apps |
| **PR-003:** [Proceso 3] | | | ✓ | | | 1 app |
| **PR-004:** [Proceso 4] | | ✓ | | ✓ | ✓ | 3 apps |
| **PR-005:** [Proceso 5] | | | | | | **GAP!** |

**Leyenda:**
- ✓ = Aplicación soporta este proceso
- (Vacío) = No soporta

---

## Matriz Detallada (con tipo de soporte)

| Proceso | Aplicación | Rol | % Cobertura | Criticidad | Observaciones |
|---------|------------|-----|-------------|------------|---------------|
| PR-001: [Proceso] | APP-001 | Primario | 80% | Alta | [Observaciones] |
|  | APP-002 | Secundario | 20% | Media | [Observaciones] |
| PR-002: [Proceso] | APP-003 | Primario | 100% | Crítica | [Observaciones] |
| PR-003: [Proceso] | - | - | 0% | Alta | **GAP: No automatizado** |

### Roles de Soporte
- **Primario:** Aplicación principal que ejecuta el proceso
- **Secundario:** Aplicación que soporta parcialmente o provee inputs/outputs
- **Auxiliar:** Aplicación que provee funciones auxiliares (reporting, auditoría)

---

## Análisis de Gaps

### Procesos Sin Cobertura de Aplicación

| Proceso ID | Proceso | Criticidad | Impacto | Acción Requerida | Prioridad |
|------------|---------|------------|---------|------------------|-----------|
| PR-005 | [Nombre] | Alta | [Descripción impacto] | Desarrollar APP-006 | ALTA |
|  |  |  |  |  |  |

### Procesos con Cobertura Parcial (<50%)

| Proceso ID | Proceso | Cobertura Actual | Gap | Acción |
|------------|---------|------------------|-----|--------|
| PR-001 | [Nombre] | 40% | 60% manual | Automatizar con APP-007 |
|  |  |  |  |  |

---

## Análisis de Redundancia

### Procesos con Múltiples Aplicaciones (posible redundancia)

| Proceso ID | Proceso | Aplicaciones | ¿Justificado? | Acción |
|------------|---------|--------------|---------------|--------|
| PR-002 | [Nombre] | APP-001, APP-002, APP-004 | ☐ Sí ☐ No | [Consolidar/Mantener/Explicar] |
|  |  |  |  |  |

**Análisis de justificación:**
- ¿Las aplicaciones cubren diferentes geografías/canales/segmentos?
- ¿Es transición temporal (migration en progreso)?
- ¿Redundancia es necesaria (HA, DR)?
- O es deuda técnica que debe remediarse?

---

## Métricas de Cobertura

### Por Proceso

| Métrica | Valor |
|---------|-------|
| Total de procesos | [#] |
| Procesos 100% automatizados | [#] ([%]) |
| Procesos parcialmente automatizados | [#] ([%]) |
| Procesos sin automatización (GAP) | [#] ([%]) |
| Procesos con redundancia | [#] ([%]) |

### Por Aplicación

| Aplicación | # Procesos Soportados | % del Total | Criticidad |
|------------|-----------------------|-------------|------------|
| APP-001 | [#] | [%] | [Alta/Media/Baja] |
| APP-002 | [#] | [%] | [Alta/Media/Baja] |

**Análisis:**
- Aplicaciones que soportan muchos procesos son críticas pero posiblemente monolíticas
- Aplicaciones que soportan pocos procesos pueden ser especializadas o candidatas para consolidación

---

## Priorización de Gaps

| Gap ID | Proceso Sin Cobertura | Impacto de Negocio | Esfuerzo de Solución | Prioridad | Roadmap |
|--------|----------------------|-------------------|---------------------|-----------|---------|
| G01 | PR-005 | Alto | Medio | ALTA | Q1 2025 |
| G02 | PR-008 | Medio | Alto | MEDIA | Q3 2025 |
| G03 | PR-012 | Bajo | Bajo | BAJA | Backlog |

---

## Roadmap de Mejora

### Q1 2025
- [Gap G01]: Desarrollar/Adquirir solución para PR-005
- [Redundancia R01]: Consolidar APP-001 y APP-002 para PR-002

### Q2 2025
- [Gap G02]: Automatizar PR-008 con APP-009

### Q3 2025
- [Optimización]: Mejorar cobertura de PR-001 de 40% a 80%

---

## Matriz AS-IS vs TO-BE

### AS-IS (Estado Actual)

| Proceso | APP-001 | APP-002 | APP-003 | Cobertura |
|---------|---------|---------|---------|-----------|
| PR-001 | ✓ | ✓ | | 2 apps |
| PR-002 | ✓ | | ✓ | 2 apps |
| PR-003 | | | | **GAP** |

### TO-BE (Estado Objetivo)

| Proceso | APP-001 | APP-NEW | APP-003 | Cobertura |
|---------|---------|---------|---------|-----------|
| PR-001 | ✓ | | | 1 app (consolidado) |
| PR-002 | | ✓ | ✓ | 2 apps (APP-NEW reemplaza APP-002) |
| PR-003 | | ✓ | | 1 app (gap cerrado) |

**Cambios clave:**
1. Consolidar APP-002 → APP-NEW
2. Cerrar gap de PR-003 con APP-NEW
3. Simplificar soporte de PR-001 (remover redundancia)

---

## Notas

[Agregar cualquier observación relevante sobre la relación proceso-aplicación]
