# Roadmap de Migración

**Proyecto:** [Nombre del proyecto]
**Fecha:** [Fecha]
**Versión:** [Versión]

## Propósito
Definir el plan detallado de migración desde la arquitectura actual (AS-IS) hacia la arquitectura objetivo (TO-BE), incluyendo secuencia, timeline, recursos y riesgos.

---

## Visión General del Roadmap

**Duración Total:** [X meses]
**Fecha de Inicio:** [Fecha]
**Fecha de Fin (Go-Live):** [Fecha]

**Inversión Total Estimada:** $[X]
- CAPEX (one-time): $[Y]
- OPEX (incremental anual): $[Z]

**Equipo Requerido:**
- [X] personas tiempo completo
- [Y] personas tiempo parcial
- [Z] consultores externos

---

## Releases/Oleadas

### Release 1: [Nombre] - [Timeline]

**Objetivo:** [Descripción del objetivo]

**Alcance:**
- [Componente/Capacidad 1]
- [Componente/Capacidad 2]
- [Componente/Capacidad 3]

**Brechas que cierra:**
- [Gap ID]: [Nombre]
- [Gap ID]: [Nombre]

**Entregables:**
- [Entregable 1]
- [Entregable 2]
- [Entregable 3]

**Valor de Negocio:**
[Descripción del valor que aporta este release]

**KPIs de Éxito:**
| Métrica | Baseline | Target | Medición |
|---------|----------|--------|----------|
| [Métrica 1] | [Valor actual] | [Valor objetivo] | [Cómo se mide] |
| [Métrica 2] | [Valor actual] | [Valor objetivo] | [Cómo se mide] |

**Estimación:**
- **Esfuerzo:** [X meses-persona]
- **Costo:** $[Y]
- **Duración:** [Z meses]

**Equipo:**
| Rol | # Personas | % Dedicación |
|-----|------------|--------------|
| [Rol 1] | [#] | [%] |
| [Rol 2] | [#] | [%] |

**Dependencias:**
- **Pre-requisitos:** [Lista de dependencias que deben completarse antes]
- **Habilita:** [Qué releases dependen de este]

**Riesgos:**
| Riesgo | Probabilidad | Impacto | Mitigación |
|--------|--------------|---------|------------|
| [Riesgo 1] | Alta/Media/Baja | Alto/Medio/Bajo | [Plan] |

**Criterios de Go/No-Go:**
- ☐ [Criterio 1]
- ☐ [Criterio 2]
- ☐ [Criterio 3]

**Estrategia de Rollout:**
- ☐ Big Bang (todo a la vez)
- ☐ Phased (por etapas)
- ☐ Blue-Green (coexistencia)
- ☐ Canary (gradual)

**Detalle de estrategia:** [Explicar]

**Plan de Rollback:**
[Descripción del plan de contingencia si falla]

---

### Release 2: [Nombre] - [Timeline]

[Repetir estructura anterior]

---

### Release 3: [Nombre] - [Timeline]

[Repetir estructura anterior]

---

## Cronograma Visual

```
Año 2025
─────────────────────────────────────────────────────────────────────
Q1                  Q2                  Q3                  Q4
│                   │                   │                   │
├─ Release 1 ───────┤                   │                   │
│  Foundation       │                   │                   │
│                   ├─ Release 2 ───────┤                   │
│                   │  Core Migration   │                   │
│                   │                   ├─ Release 3 ───────┤
│                   │                   │  Advanced         │
│                   │                   │                   ├─ Release 4 ───┤
│                   │                   │                   │  Optimization  │
│                   │                   │                   │                │
M1                  M2                  M3                  M4 (GO-LIVE)
└───────────────────┴───────────────────┴───────────────────┴────────────────

Milestones:
M1: [Descripción hito 1]
M2: [Descripción hito 2]
M3: [Descripción hito 3]
M4: [Go-live / Descripción hito final]
```

---

## Hitos (Milestones)

### M1: [Nombre del Hito] - [Fecha]

**Descripción:** [Qué representa este hito]

**Criterios de Cumplimiento:**
- ☐ [Criterio 1]
- ☐ [Criterio 2]
- ☐ [Criterio 3]

**Entregables Requeridos:**
- [Entregable 1]
- [Entregable 2]

**Aprobadores:** [Quién debe aprobar este hito]

**Go/No-Go Meeting:** [Fecha de reunión de decisión]

---

### M2: [Nombre del Hito] - [Fecha]

[Repetir estructura]

---

## Matriz de Transición

Muestra el estado de cada componente en cada fase:

| Componente | AS-IS | Release 1 | Release 2 | Release 3 | TO-BE Final | Fecha Target |
|------------|-------|-----------|-----------|-----------|-------------|--------------|
| Frontend | Legacy PHP | Coexiste | Migrado | Migrado | React SPA | Q2 2025 |
| Backend API | Monolito | Coexiste | Microservices | Microservices | Microservices | Q3 2025 |
| Database | Oracle on-prem | Replicación | PostgreSQL RDS | PostgreSQL RDS | PostgreSQL RDS | Q2 2025 |
| Cache | Local | Redis | Redis | Redis | Redis | Q1 2025 |
| Infra | On-premise | Hybrid | Cloud (pilot) | Cloud (prod) | Cloud | Q3 2025 |

**Leyenda:**
- **Coexiste:** Sistema viejo y nuevo funcionan en paralelo
- **Migrado:** Completamente migrado al nuevo
- **Replicación:** Datos replicándose entre viejo y nuevo
- **Hybrid:** Parte en viejo, parte en nuevo

---

## Plan de Migración de Datos

### Estrategia General

☐ **Big Bang:** Migración completa en ventana de mantenimiento
☐ **Trickle Migration:** Migración gradual por lotes
☐ **Parallel Run:** Ambos sistemas operan con sincronización
☐ **Phased by Entity:** Migrar entidad por entidad

**Estrategia elegida:** [Explicar]

### Secuencia de Migración de Datos

| Orden | Entidad | Volumen | Método | Duración | Ventana | Rollback Plan |
|-------|---------|---------|--------|----------|---------|---------------|
| 1 | [Entidad A] | [#GB] | [Bulk load] | [X hrs] | [Día/hora] | [Plan] |
| 2 | [Entidad B] | [#GB] | [Streaming] | [Y días] | [Periodo] | [Plan] |
| 3 | [Entidad C] | [#GB] | [Bulk + CDC] | [Z días] | [Periodo] | [Plan] |

### Validación de Integridad

| Paso | Check | Herramienta | Criterio de Éxito |
|------|-------|-------------|-------------------|
| 1 | Row count | SQL queries | 100% match |
| 2 | Checksums | MD5/SHA | 100% match |
| 3 | Business rules | Custom scripts | >99.9% match |
| 4 | Sampling | Manual verification | 100% of sample |

### Plan de Cutover

**Preparación (D-7 a D-1):**
- D-7: Code freeze en sistema legacy
- D-5: Backup completo + validación
- D-3: Migración inicial (bulk)
- D-1: Rehearsal completo
- D-1: Go/no-go meeting

**Día del Cutover (Día D):**

| Hora | Actividad | Responsable | Duración | Check |
|------|-----------|-------------|----------|-------|
| 18:00 | Comunicación a usuarios (downtime starts) | Comms | 15min | ☐ |
| 18:15 | Apagar aplicaciones legacy | Ops | 15min | ☐ |
| 18:30 | Backup final | DBA | 30min | ☐ |
| 19:00 | Migración incremental (últimas horas) | DBA | 2hrs | ☐ |
| 21:00 | Validación de integridad | QA | 1hr | ☐ |
| 22:00 | Smoke testing de nuevas aplicaciones | QA | 1hr | ☐ |
| 23:00 | Switch DNS / Load balancer | DevOps | 15min | ☐ |
| 23:15 | Smoke testing con tráfico real | QA | 45min | ☐ |
| 00:00 | **GO/NO-GO DECISION** | CTO + PM | 15min | ☐ |
| 00:15 | Apertura del servicio (si GO) | Ops | 15min | ☐ |

**Plan de Rollback:**
- **Trigger:** [Condiciones que activan rollback]
- **RTO:** [X horas] para volver a operación
- **Proceso:**
  1. Revertir DNS/LB a legacy
  2. Re-sincronizar datos desde backup
  3. Reiniciar aplicaciones legacy
  4. Validar operación
- **Punto de no retorno:** [Hora después de la cual rollback ya no es viable]

**Post-Cutover (D+1 a D+7):**
- D+1: Monitoreo 24/7, war room activa
- D+3: Revisión de incidentes, tuning
- D+7: Retrospectiva, apagado definitivo de legacy

---

## Gestión de Riesgos

### Top 10 Riesgos del Roadmap

| Rank | Riesgo | Probabilidad | Impacto | Exposición | Owner | Mitigación | Contingencia |
|------|--------|--------------|---------|------------|-------|------------|--------------|
| 1 | [Riesgo 1] | Alta | Crítico | 9 | [Owner] | [Plan preventivo] | [Plan reactivo] |
| 2 | [Riesgo 2] | Media | Alto | 6 | [Owner] | [Plan preventivo] | [Plan reactivo] |

**Exposición = Probabilidad × Impacto**
- Probabilidad: Baja=1, Media=2, Alta=3
- Impacto: Bajo=1, Medio=2, Alto=3, Crítico=4

### Riesgos por Release

**Release 1:**
- [Riesgo A]: [Descripción y mitigación]
- [Riesgo B]: [Descripción y mitigación]

**Release 2:**
- [Riesgo C]: [Descripción y mitigación]
- [Riesgo D]: [Descripción y mitigación]

---

## Plan de Recursos

### Staffing por Release

| Release | Rol | # Personas | Dedicación | Duración | Costo |
|---------|-----|------------|------------|----------|-------|
| R1 | Solution Architect | 1 | 100% | 3 meses | $45k |
| R1 | Cloud Engineer | 2 | 100% | 3 meses | $60k |
| R1 | Developer | 3 | 100% | 3 meses | $75k |
| R2 | Solution Architect | 1 | 50% | 4 meses | $30k |
| R2 | Developer | 5 | 100% | 4 meses | $150k |
| ... | ... | ... | ... | ... | ... |

### Staffing Chart

```
                 Q1          Q2          Q3          Q4
Architects      ████████    ████        ██          ██
Cloud Eng       ████████    ████████    ████
Backend Dev                 ████████    ████████    ██
Frontend Dev                ████        ████
DBA             ████        ████████    ████
QA                          ██          ████        ████
Security        ██          ██          ██          ██

Total FTEs:       8           12          10          6
```

### Contrataciones Requeridas

| Rol | Cantidad | Tipo | Timeline | Justificación |
|-----|----------|------|----------|---------------|
| Cloud Architect | 1 | Full-time | Antes Q1 | Expertise en AWS ausente |
| DevOps Engineer | 2 | Full-time | Antes Q1 | Implementar IaC y CI/CD |
| React Developer | 1 | Contractor | Q2 | Peak de desarrollo frontend |

---

## Presupuesto

### Inversión por Release

| Release | Staffing | Infraestructura | Licencias | Consultoría | Contingencia (15%) | Total |
|---------|----------|-----------------|-----------|-------------|--------------------|-------|
| R1 | $200k | $50k | $30k | $50k | $50k | $380k |
| R2 | $350k | $80k | $40k | $100k | $86k | $656k |
| R3 | $250k | $60k | $20k | $50k | $57k | $437k |
| R4 | $150k | $40k | $10k | $20k | $33k | $253k |
| **TOTAL** | **$950k** | **$230k** | **$100k** | **$220k** | **$226k** | **$1,726k** |

### CAPEX vs OPEX

**CAPEX (One-time):**
- Staffing: $950k
- Migration tools: $50k
- Consultoría: $220k
- Training: $80k
- Contingencia: $226k
- **Total CAPEX:** **$1,526k**

**OPEX (Run-rate post-migration):**
- Cloud infrastructure: $25k/mes
- Licencias SaaS: $8k/mes
- Monitoreo/Tooling: $3k/mes
- **Total OPEX:** **$36k/mes** ($432k/año)

**Comparación:**
- OPEX actual (on-premise): $55k/mes ($660k/año)
- OPEX nuevo (cloud): $36k/mes ($432k/año)
- **Ahorro anual:** $228k/año (35% reducción)
- **Payback period:** ~7 meses

---

## Plan de Comunicación

### Stakeholders y Frecuencia

| Stakeholder | Audiencia | Frecuencia | Canal | Contenido |
|-------------|-----------|------------|-------|-----------|
| Ejecutivos | CEO, CFO, CTO | Mensual | Presentación | Status, ROI, riesgos |
| Sponsors | VP Engineering | Quincenal | Meeting | Progreso detallado, decisiones |
| Tech Leads | Equipo técnico | Semanal | Standup | Daily work, blockers |
| Business | Product, Ops | Quincenal | Email | Impacto en negocio, timeline |
| Usuarios | End users | Pre-release | Email + Training | Cambios, nueva funcionalidad |

### Comunicaciones Clave

| Hito | Cuándo | Audiencia | Mensaje | Canal |
|------|--------|-----------|---------|-------|
| Kick-off | Inicio | Toda la org | Proyecto inicia, visión, timeline | All-hands + email |
| Release 1 | Pre-deploy | Usuarios | Qué cambia, cuándo, cómo les afecta | Email + training |
| M2 | Milestone | Ejecutivos | 50% completado, on track | Presentación |
| Go-Live | Launch | Toda la org | Sistema nuevo en producción | All-hands + email |
| Post-mortem | Post | Equipo | Lecciones aprendidas | Workshop |

---

## Métricas y Tracking

### KPIs del Roadmap

| KPI | Target | Medición | Frecuencia |
|-----|--------|----------|------------|
| % Completado del roadmap | 100% en [Fecha] | Releases completados / Total | Mensual |
| Adherencia al presupuesto | ±10% | Gasto real vs estimado | Mensual |
| Adherencia al timeline | ±2 semanas | Fecha real vs planeada | Semanal |
| Calidad (bugs críticos) | <5 por release | Count en producción | Por release |
| Disponibilidad (uptime) | >99.9% | Monitoreo | Continuo |
| Satisfacción del usuario | >4/5 | Survey | Post cada release |

### Dashboard de Progreso

**Estado General:**
- ☐ On Track (verde)
- ☐ At Risk (amarillo)
- ☐ Off Track (rojo)

**Releases:**
- Release 1: ☑ Completado (fecha)
- Release 2: ☐ In Progress (60% completado)
- Release 3: ☐ Not Started
- Release 4: ☐ Not Started

**Presupuesto:**
- Gastado: $X / $1,726k ([%])
- Forecast: $Y (on track / at risk / over budget)

**Timeline:**
- Semanas transcurridas: [X]
- Semanas restantes: [Y]
- Estado: On schedule / 2 weeks delay / etc.

**Riesgos:**
- Riesgos activos: [#]
- Riesgos materializados: [#]
- Mitigaciones en progreso: [#]

---

## Lecciones Aprendidas (Post-Mortem)

Completar al finalizar cada release:

### Release 1: [Nombre]

**¿Qué salió bien?**
- [Aspecto 1]
- [Aspecto 2]

**¿Qué no salió bien?**
- [Problema 1]
- [Problema 2]

**¿Qué aprendimos?**
- [Aprendizaje 1]
- [Aprendizaje 2]

**Acciones para siguiente release:**
- [Acción 1]
- [Acción 2]

---

## Anexos

### A. Glosario de Términos

| Término | Definición |
|---------|------------|
| [Término 1] | [Definición] |
| [Término 2] | [Definición] |

### B. Referencias

- [Documento de Arquitectura Objetivo]
- [Análisis de Brechas]
- [Business Case]

### C. Contactos Clave

| Rol | Nombre | Email | Teléfono |
|-----|--------|-------|----------|
| Project Sponsor | [Nombre] | [Email] | [Tel] |
| Architecture Owner | [Nombre] | [Email] | [Tel] |
| Release Manager | [Nombre] | [Email] | [Tel] |

---

## Control de Cambios

| Versión | Fecha | Autor | Cambios |
|---------|-------|-------|---------|
| 1.0 | [Fecha] | [Autor] | Versión inicial |
| 1.1 | [Fecha] | [Autor] | [Cambios realizados] |

---

## Aprobaciones

| Rol | Nombre | Firma | Fecha |
|-----|--------|-------|-------|
| Project Sponsor | [Nombre] | | |
| CTO | [Nombre] | | |
| CFO | [Nombre] | | |
| Architecture Owner | [Nombre] | | |
