# Catálogo de Capacidades de Negocio

**Proyecto:** [Nombre del proyecto]
**Fecha:** [Fecha]
**Versión:** [Versión]

## Propósito
Documentar las capacidades de negocio que la organización posee actualmente y las que necesitará para ejecutar su estrategia.

---

## Mapa de Capacidades

### Nivel 1 - Capacidades Principales

```
┌─────────────────┬─────────────────┬─────────────────┬─────────────────┐
│   [Capacidad 1] │   [Capacidad 2] │   [Capacidad 3] │   [Capacidad 4] │
│                 │                 │                 │                 │
└─────────────────┴─────────────────┴─────────────────┴─────────────────┘
```

---

## Catálogo Detallado de Capacidades

| ID | Capacidad | Nivel | Descripción | Propietario | Estado AS-IS | Estado TO-BE | Gap | Prioridad |
|----|-----------|-------|-------------|-------------|--------------|--------------|-----|-----------|
| CAP-001 | [Nombre] | 1 | [Descripción] | [Owner] | [Nivel 0-5] | [Nivel 0-5] | [+/-X] | Alta/Media/Baja |
| CAP-002 | [Nombre] | 2 | [Descripción] | [Owner] | [Nivel 0-5] | [Nivel 0-5] | [+/-X] | Alta/Media/Baja |
|  |  |  |  |  |  |  |  |  |

### Niveles de Madurez

**0 - No existe:** La capacidad no está presente en la organización

**1 - Inicial/Ad-hoc:**
- Procesos no documentados
- Ejecución inconsistente
- Dependiente de individuos

**2 - Repetible pero manual:**
- Procesos documentados básicamente
- Ejecución manual pero consistente
- Algunos procedimientos establecidos

**3 - Definido y documentado:**
- Procesos completamente documentados
- Ejecución estandarizada
- Capacitación formal

**4 - Gestionado y medido:**
- Métricas y KPIs establecidos
- Monitoreo continuo
- Mejora basada en datos

**5 - Optimizado y automatizado:**
- Altamente automatizado
- Mejora continua sistemática
- Innovación constante

---

## Detalle por Capacidad

### CAP-001: [Nombre de la Capacidad]

**Nivel:** [1/2/3 - indica jerarquía]

**Descripción completa:**
[Descripción detallada de qué hace esta capacidad y por qué es importante]

**Propietario de Negocio:** [Nombre y rol]

**Criticidad:** ☐ Crítica  ☐ Alta  ☐ Media  ☐ Baja

**Estado Actual (AS-IS):**
- **Nivel de Madurez:** [0-5]
- **Cómo se ejecuta hoy:** [Descripción]
- **Fortalezas:**
  - [Fortaleza 1]
  - [Fortaleza 2]
- **Debilidades:**
  - [Debilidad 1]
  - [Debilidad 2]

**Estado Objetivo (TO-BE):**
- **Nivel de Madurez Target:** [0-5]
- **Cómo debe ejecutarse:** [Descripción]
- **Cambios necesarios:**
  - [Cambio 1]
  - [Cambio 2]

**Gap Analysis:**
- **Gap de madurez:** [+/- X niveles]
- **Tipo de gap:**
  - ☐ Capacidad nueva (no existe hoy)
  - ☐ Mejora de capacidad existente
  - ☐ Transformación de capacidad
  - ☐ Eliminación de capacidad

**Dependencias:**
- Depende de: [CAP-XXX, CAP-YYY]
- Es requerida por: [CAP-ZZZ]

**Procesos que habilita:**
- [Proceso 1]
- [Proceso 2]

**Aplicaciones que soportan:**
- AS-IS: [Aplicación actual]
- TO-BE: [Aplicación futura]

**Métricas clave:**
| Métrica | AS-IS | TO-BE | Target |
|---------|-------|-------|--------|
| [Métrica 1] | [Valor actual] | [Valor objetivo] | [Fecha] |
| [Métrica 2] | [Valor actual] | [Valor objetivo] | [Fecha] |

---

### CAP-002: [Nombre de la Capacidad]

[Repetir estructura anterior]

---

## Análisis de Brechas Consolidado

### Capacidades Críticas con Brechas Mayores

| Capacidad | Gap | Impacto si no se cierra | Esfuerzo | Prioridad | Plan |
|-----------|-----|-------------------------|----------|-----------|------|
| [Nombre]  | +3  | [Descripción impacto]   | Alto     | CRÍTICO   | [Acción] |
|           |     |                         |          |           |      |

### Capacidades Nuevas a Crear

| Capacidad | Rationale | Owner | Timeline | Dependencias |
|-----------|-----------|-------|----------|--------------|
| [Nombre]  | [Por qué se necesita] | [Owner] | [Q1 2025] | [Otras capacidades] |
|           |           |       |          |              |

### Capacidades a Deprecar/Eliminar

| Capacidad | Razón para eliminar | Impacto | Plan de transición |
|-----------|---------------------|---------|-------------------|
| [Nombre]  | [Razón]             | [Impacto] | [Plan]          |
|           |                     |         |                   |

---

## Mapa de Calor de Capacidades

Visualización de madurez actual vs criticidad:

```
Alta     │ [CAP-003]              │ [CAP-001] ✓
Criticid │                        │ [CAP-005] ✓
ad       │                        │
         │ [CAP-004]              │ [CAP-002] !
Baja     │ [CAP-006]              │
         └────────────────────────┴────────────
          Baja Madurez             Alta Madurez

✓ = OK (alta criticidad + alta madurez)
! = URGENTE (alta criticidad + baja madurez)
```

**Interpretación:**
- **Cuadrante superior derecho (✓):** Capacidades en buen estado, mantener
- **Cuadrante superior izquierdo (!):** ATENCIÓN - alta criticidad pero baja madurez, priorizar
- **Cuadrante inferior izquierdo:** Baja prioridad de inversión
- **Cuadrante inferior derecho:** Oportunidad de optimización/simplificación

---

## Roadmap de Capacidades

| Capacidad | Q1 | Q2 | Q3 | Q4 | Hito |
|-----------|----|----|----|----|------|
| [CAP-001] | ████ | ████ |  |  | Nivel 4 |
| [CAP-002] |  | ████ | ████ |  | Nivel 3 |
| [CAP-003] |  |  | ████ | ████ | Nivel 5 |

---

## Notas

[Cualquier nota adicional sobre capacidades, supuestos, riesgos, etc.]
