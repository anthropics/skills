# Exemplos de Aplicação - Caio Villani Agent

## Exemplo 1: Análise Estratégica - Ampliação de Cobertura do CAPS

### Cenário

Município de médio porte (50.000 habitantes) possui CAPS I com cobertura atual de 0,50/100.000 habitantes (parâmetro MS: 0,70-1,00). Gestão solicita análise estratégica para ampliação.

### Aplicação do PES

**Momento Explicativo**:

**Nó crítico identificado**: Cobertura abaixo do parâmetro nacional, com lista de espera de 45 dias para primeiro atendimento.

**Fluxograma situacional**:
```
CAUSAS                           PROBLEMA                CONSEQUÊNCIAS
↓                                    ↓                          ↓
Equipe subdimensionada     →    Baixa cobertura CAPS    →   Agravamento de casos
Horário restrito (8h-17h)  →    (0,50/100k hab)         →   Sobrecarga da emergência
Alta rotatividade de RH    →                            →   Baixa resolutividade APS
Desarticulação com APS     →                            →   Internações evitáveis
```

**Análise de atores**:

| Ator | Interesse | Motivação | Força | Estratégia |
|------|-----------|-----------|-------|------------|
| Equipe CAPS | Reduzir sobrecarga | 5 | 2 | Fortalecer com contratações |
| Secretaria Saúde | Cumprir indicadores | 4 | 5 | Demonstrar custo-benefício |
| Secretaria Fazenda | Controlar gastos | 2 | 4 | Evidenciar economia em internações |
| APS (ESF) | Apoio matricial | 3 | 3 | Capacitação + fluxo claro |
| Usuários | Acesso rápido | 5 | 1 | Incluir em conselhos |

**Análise de governabilidade**:

- **Alta governabilidade**: Reorganização de agenda, protocolos de fluxo, capacitação de APS
- **Governabilidade compartilhada**: Contratação de profissionais (depende de aprovação da Secretaria de Fazenda), ampliação de horário (requer recursos)
- **Fora de governabilidade**: Prevalência de transtornos mentais na população, estigma social estrutural

**Momento Normativo**:

**Objetivo**: Alcançar cobertura de 0,80/100.000 habitantes em 18 meses, com redução de tempo de espera para 15 dias.

**Operações prioritárias**:

1. **Reestruturação de fluxo**: Acolhimento a demanda espontânea + agendamento por gravidade
2. **Ampliação de equipe**: Contratar 1 psiquiatra (20h), 1 psicólogo (40h), 1 terapeuta ocupacional (40h)
3. **Matriciamento da APS**: Supervisão mensal + telessaúde para casos leves/moderados
4. **Ampliação de horário**: Funcionamento até 20h em 2 dias/semana
5. **Grupos terapêuticos**: 4 grupos semanais (ansiedade, depressão, famílias, psicoeducação)

**Momento Estratégico**:

**Cenário realista**: Aprovação de 2 novos profissionais (psicólogo + terapeuta ocupacional) em 6 meses, ampliação de horário em 12 meses, matriciamento iniciado imediatamente.

**Trajetória estratégica**:
1. Iniciar operações de baixo custo imediatamente (reestruturação de fluxo, matriciamento)
2. Demonstrar redução de custos em internações e emergências nos primeiros 6 meses
3. Apresentar relatório técnico-financeiro para Secretaria de Fazenda
4. Com evidências de impacto, negociar contratações e ampliação de horário

**Momento Tático-Operacional**:

**Cronograma executivo (primeiros 6 meses)**:

| Mês | Operação | Responsável | Indicador |
|-----|----------|-------------|-----------|
| 1 | Novo protocolo de acolhimento | Coord. CAPS | 100% casos triados em 48h |
| 1-2 | Capacitação APS em saúde mental | Coord. RAPS | 80% ESF capacitadas |
| 2 | Início grupos terapêuticos | Equipe CAPS | 2 grupos/semana ativos |
| 3 | Primeira reunião de matriciamento | Psiquiatra CAPS | 100% ESF participando |
| 4-6 | Coleta de dados pré-intervenção | Analista de dados | Relatório pronto mês 6 |
| 6 | Apresentação de resultados à gestão | Coord. RAPS | Aprovação fase 2 |

### Output esperado do agente

O agente forneceria:

1. **Análise situacional densa** (2-3 parágrafos BLUF com conclusão principal)
2. **Fluxograma situacional** em formato Markdown/Mermaid
3. **Matriz de atores** com estratégias específicas
4. **Trajetória estratégica** viável considerando restrições políticas-financeiras
5. **Cronograma executivo** com indicadores de processo e resultado
6. **Análise de riscos** e planos de contingência
7. **Referências**: Portaria 336/2002, Portaria 3.088/2011, parâmetros MS

---

## Exemplo 2: Elaboração de Protocolo Clínico - Transtorno de Ansiedade Generalizada

### Cenário

CAPS I necessita protocolo para manejo de Transtorno de Ansiedade Generalizada (TAG) na população adulta, integrando abordagens farmacológicas e psicossociais.

### Aplicação do Evidence-Based Practice

**1. Melhor evidência científica**:

Busca estruturada:
- **Cochrane Library**: "Generalised anxiety disorder AND treatment" (última revisão sistemática 2021)
- **PubMed**: Filtro clinical trials, últimos 5 anos, metanálises
- **Diretrizes**: NICE (UK), APA (USA), CFM/ABP (Brasil)

Evidências consolidadas:
- **Farmacológico**: ISRSs (escitalopram, paroxetina) e ISRNs (venlafaxina, duloxetina) são primeira linha (NNT 5-6, evidência grau A)
- **Psicoterapia**: TCC estruturada mostra eficácia equivalente a farmacoterapia (evidência grau A), ACT e terapia psicodinâmica breve têm evidência moderada (grau B)
- **Combinação**: Farmacoterapia + TCC tem efeito superior isoladamente a longo prazo (evidência grau A)
- **Intervenções complementares**: Exercício físico regular, mindfulness, higiene do sono têm evidência moderada como adjuvantes

**2. Expertise da equipe**:

Reunião multiprofissional identifica:
- População atendida tem baixa adesão a medicação contínua (cultural: "remédio vicia")
- Grupos terapêuticos têm melhor aceitação que atendimento individual para casos leves
- Barreiras: dificuldade de transporte para sessões semanais prolongadas
- Facilitadores: boa resposta a psicoeducação, apoio de agentes comunitários de saúde

**3. Valores e preferências dos usuários**:

Assembleia de usuários e familiares revela:
- Preferência por abordagens não medicamentosas quando possível
- Interesse em técnicas de autogerenciamento
- Demanda por grupos de apoio entre pares
- Preocupação com efeitos colaterais de medicações

### Protocolo elaborado (estrutura)

**Título**: Protocolo de Manejo do Transtorno de Ansiedade Generalizada no CAPS I - Extrema-MG

**1. Definição e critérios diagnósticos** (DSM-5, CID-11)

**2. Estratificação de gravidade**:
- **Leve**: GAD-7 ≤ 9, funcionalidade preservada
- **Moderada**: GAD-7 10-14, comprometimento funcional leve-moderado
- **Grave**: GAD-7 ≥ 15, comprometimento funcional importante

**3. Fluxograma de tratamento**:

```
Triagem (GAD-7)
    ↓
Avaliação diagnóstica → Sim TAG → Estratificação de gravidade
                            ↓
              ┌─────────────┼─────────────┐
              ↓             ↓             ↓
          LEVE        MODERADA        GRAVE
              ↓             ↓             ↓
    Psicoeducação    TCC grupo    Consulta psiquiátrica
    Grupo ansiedade  + Avaliação  + TCC individual
    Reavaliação 4sem  psiquiátrica + Farmacoterapia
                      ↓             ↓
                  Farmacoterapia   Reavaliação 2sem
                  se necessária
                      ↓             ↓
                  Reavaliação 4sem  Ajuste conforme resposta
```

**4. Intervenções por nível**:

**Leve**:
- Psicoeducação (2 sessões): natureza da ansiedade, fatores mantenedores, técnicas de autogerenciamento
- Grupo terapêutico "Vencendo a Ansiedade" (8 sessões semanais, formato TCC): psicoeducação, reestruturação cognitiva, exposição gradual, prevenção de recaída
- Orientações de higiene do sono, exercício físico, redução de cafeína/álcool
- Reavaliação GAD-7 após 4 semanas

**Moderada**:
- Tudo acima +
- Avaliação psiquiátrica para considerar farmacoterapia
- Farmacoterapia primeira linha: Escitalopram 10-20mg/dia OU Sertralina 50-200mg/dia
- Explicar: efeito gradual (2-4 semanas), possíveis efeitos colaterais iniciais, importância de adesão mínima 6-12 meses
- TCC em grupo ou individual conforme disponibilidade e preferência
- Reavaliação 2 semanas (tolerabilidade), 4 semanas (eficácia inicial), 8 semanas (resposta)

**Grave**:
- Consulta psiquiátrica prioritária (até 7 dias)
- Farmacoterapia imediata
- TCC individual (quando disponível) ou grupo adaptado
- Considerar encaminhamento para serviços especializados se refratário
- Avaliar comorbidades (depressão, uso de substâncias)
- Reavaliação semanal nas primeiras 4 semanas

**5. Critérios de resposta**:
- **Resposta**: Redução ≥ 50% GAD-7 ou GAD-7 < 10
- **Remissão**: GAD-7 ≤ 5 + funcionalidade restaurada
- **Não resposta**: < 25% redução GAD-7 após 8 semanas em dose adequada

**6. Manejo de não resposta**:
- Revisar adesão, comorbidades, estressores psicossociais
- Considerar troca de ISRS ou mudar para ISRN
- Intensificar psicoterapia
- Discussão em reunião de equipe
- Considerar referência para serviço terciário

**7. Indicadores de monitoramento**:
- % de casos com TAG que iniciaram tratamento em até 15 dias
- % de casos com reavaliação GAD-7 em 4 e 8 semanas
- Taxa de resposta aos 3 meses
- Taxa de adesão ao grupo terapêutico
- Taxa de abandono de tratamento

**8. Referências bibliográficas**:
- National Institute for Health and Care Excellence. Generalised anxiety disorder and panic disorder in adults. NICE guideline [NG122]. 2019.
- Bandelow B, et al. Treatment of anxiety disorders. Dialogues Clin Neurosci. 2017;19(2):93-107.
- Portaria GM/MS 336/2002. Estabelece CAPS e suas modalidades de atendimento.

### Output esperado do agente

O agente forneceria:

1. **Protocolo completo** em formato Markdown com fluxogramas
2. **Fundamentação científica** com referências verificáveis
3. **Adaptações locais** justificadas (ex: preferência por grupos devido a recursos limitados)
4. **Integração de três pilares** EBP explicitamente documentada
5. **Linguagem técnica** mas acessível para equipe multiprofissional
6. **Indicadores operacionais** para monitoramento de implementação
7. **Material de apoio**: script de psicoeducação, escala GAD-7 validada em português

---

## Exemplo 3: Análise de Indicadores Epidemiológicos

### Cenário

Análise trimestral de indicadores do CAPS I para relatório de gestão e identificação de nós críticos.

### Dados fornecidos (exemplo)

**População**: 50.000 habitantes

**Produção trimestral**:
- Atendimentos individuais: 450
- Atendimentos em grupo: 180
- Usuários ativos: 120
- Novos usuários: 35
- Abandonos: 18
- Altas: 8
- Encaminhamentos para internação: 4

**Dados nacionais de referência** (DATASUS, ano anterior):
- Cobertura CAPS recomendada: 0,70-1,00/100k hab
- Taxa de abandono média: 15-20%
- Razão atendimentos grupo/individual: 1:3

### Análise estruturada

**1. Cálculo de indicadores**:

| Indicador | Cálculo | Resultado | Parâmetro MS | Avaliação |
|-----------|---------|-----------|-------------|-----------|
| Cobertura | (120/50.000) × 100.000 | 240/100k | 700-1000/100k | **Muito abaixo** |
| Taxa de abandono | (18/120) × 100 | 15% | 15-20% | Adequado |
| Razão grupo/individual | 180/450 | 1:2,5 | 1:3 | Levemente acima |
| Taxa de internação | (4/120) × 100 | 3,3% | <5% | Adequado |
| Taxa de renovação | (35/120) × 100 | 29% trimestral | - | Alta renovação |

**2. Interpretação contextualizada**:

**Cobertura crítica**: Com 240 usuários ativos/100k habitantes, o serviço cobre apenas 24-34% da necessidade estimada (baseado em prevalência de transtornos mentais moderados-graves na população, estimada em 3-5% segundo OMS). Isso sugere:
- Demanda reprimida significativa na APS
- Possível subdiagnostico ou subnotificação
- Lista de espera não capturada nos dados

**Taxa de abandono controlada**: 15% está dentro do esperado, indicando adequada capacidade de vinculação. Manter estratégias atuais de acolhimento e acompanhamento.

**Alta taxa de renovação**: 29% de usuários novos no trimestre (projeção anual de 100%+ de rotatividade) sugere:
- Boa capacidade de dar altas/transferir para APS casos estabilizados
- Ou: Abandono não captado adequadamente como "abandono" mas registrado como "desligamento"
- Verificar se há re-internações frequentes (revolving door)

**Uso adequado de internação**: 3,3% de usuários encaminhados para internação no trimestre está abaixo de 5%, alinhado com princípio de cuidado comunitário. Manter estratégia de manejo de crises no território.

**3. Hipóteses causais para baixa cobertura**:

- **Lado da oferta**: Equipe subdimensionada, horário de funcionamento restrito, falta de divulgação do serviço
- **Lado da demanda**: Estigma, desconhecimento do serviço, barreiras de acesso (transporte, horário incompatível com trabalho)
- **Fluxo**: APS não referencia adequadamente, critérios de inclusão muito restritivos

**4. Recomendações acionáveis**:

**Imediatas (sem custo adicional)**:
1. Levantar lista de espera atual e tempo médio de espera
2. Analisar perfil de usuários atendidos (transtornos mais frequentes, faixa etária, origem da referência)
3. Reunião com coordenadores de APS para mapear demanda não referenciada
4. Revisar critérios de alta e possibilidade de contra-referência mais ágil para APS

**Curto prazo (3-6 meses)**:
1. Implementar grupos terapêuticos adicionais para aumentar capacidade de atendimento
2. Iniciar matriciamento sistemático da APS (1 reunião mensal/ESF)
3. Campanha de divulgação em parceria com ACS

**Médio prazo (6-12 meses)**:
1. Ampliação de equipe (conforme análise estratégica anterior)
2. Estudo de viabilidade de funcionamento estendido (noturno ou sábado)
3. Implementação de telessaúde para seguimento de casos estáveis

**5. Próximos passos de análise**:

- Cruzar dados com emergências psiquiátricas (quantos casos graves não são referenciados ao CAPS?)
- Analisar série temporal de 12 meses para identificar sazonalidade
- Comparar com indicadores de municípios similares na região
- Coletar dados qualitativos (satisfação de usuários, percepção de equipe sobre demanda não atendida)

### Output esperado do agente

O agente forneceria:

1. **Tabela de indicadores** calculados com interpretação
2. **Análise crítica** em linguagem acessível (evitar apenas números sem interpretação)
3. **Contextualização territorial** (comparar com parâmetros nacionais, mas interpretar localmente)
4. **Hipóteses causais** fundamentadas
5. **Recomendações priorizadas** por viabilidade e impacto esperado
6. **Próximos passos** para aprofundamento analítico
7. **Visualizações sugeridas** para relatório de gestão (gráficos de cobertura, evolução trimestral)
8. **Referências**: Portarias MS, dados DATASUS, parâmetros de cobertura

---

## Exemplo 4: Feedback Crítico Estruturado - Revisão de Plano de Trabalho

### Cenário

Psicólogo do CAPS apresenta plano de trabalho para novo grupo terapêutico. Agente deve fornecer feedback crítico construtivo.

### Plano apresentado (resumo)

**Título**: "Grupo de Apoio para Pessoas com Depressão"

**Objetivo**: "Ajudar pessoas com depressão a se sentirem melhor e terem mais qualidade de vida"

**Metodologia**: "Encontros semanais de 1h30 com roda de conversa, onde os participantes poderão compartilhar suas experiências e receber apoio do grupo"

**Critérios de inclusão**: "Pessoas com diagnóstico de depressão atendidas no CAPS"

**Número de participantes**: "Até 15 pessoas"

**Duração**: "Grupo aberto, sem término definido"

### Feedback estruturado do agente

**Avaliação geral**: O plano apresenta intenção terapêutica válida, mas carece de estruturação técnica para garantir efetividade e monitoramento. Recomendo reformulação em 5 pontos críticos antes de implementação.

---

**1. Objetivos terapêuticos pouco operacionalizados**

**Problema identificado**: Objetivo "ajudar a se sentir melhor" é vago e não permite avaliação de efetividade.

**Fundamentação**: Evidence-based practice requer objetivos mensuráveis com desfechos claramente definidos. Literatura de grupos terapêuticos em depressão (Cuijpers et al., 2020) indica que intervenções estruturadas com metas específicas têm efeito superior a apoio não-estruturado.

**Recomendação**:
Redefinir objetivos usando critérios SMART:
- "Reduzir sintomas depressivos medidos por PHQ-9 em ≥30% ao final de 12 sessões"
- "Aumentar engajamento em atividades prazerosas (behavioral activation) reportado semanalmente"
- "Desenvolver estratégias de enfrentamento de pensamentos disfuncionais identificadas individualmente"

**Ação concreta**: Incluir aplicação de PHQ-9 pré-grupo, na 6ª sessão e pós-grupo (12ª sessão).

---

**2. Metodologia insuficientemente estruturada**

**Problema identificado**: "Roda de conversa" sem estrutura pode resultar em ventilação emocional sem ganho terapêutico sustentado, além de risco de reforço de cognições disfuncionais entre participantes.

**Fundamentação**: Revisão Cochrane de psicoterapias de grupo para depressão (de Mello et al., 2005, atualização 2019) mostra que grupos estruturados (TCC, ACT, IPT) têm tamanho de efeito moderado-alto (d=0,65), enquanto grupos de suporte não-estruturado têm efeito pequeno (d=0,25).

**Recomendação**:
Incorporar elementos de TCC em grupo (modelo Lewinsohn ou Mind Over Mood adaptado):
- Sessões 1-2: Psicoeducação sobre depressão (modelo cognitivo-comportamental)
- Sessões 3-4: Identificação de pensamentos automáticos negativos
- Sessões 5-7: Ativação comportamental estruturada
- Sessões 8-10: Reestruturação cognitiva
- Sessões 11-12: Prevenção de recaída e plano de manutenção

**Alternativa**: Se equipe não tem formação em TCC, considerar grupo de Ativação Comportamental (mais simples de implementar, evidência robusta em depressão leve-moderada).

**Ação concreta**: Elaborar roteiro de sessões com objetivos específicos, materiais de apoio (handouts) e exercícios para casa.

---

**3. Critérios de inclusão muito amplos**

**Problema identificado**: "Pessoas com depressão" abrange desde depressão leve até grave, episódio único ou recorrente, com comorbidades ou não. Grupo heterogêneo demais pode dificultar adesão e efetividade.

**Fundamentação**: Literatura de dinâmica de grupos terapêuticos (Yalom & Leszcz, 2020) indica que coesão grupal e sentimento de universalidade aumentam quando participantes compartilham características e objetivos similares.

**Recomendação**:
Definir critérios de inclusão e exclusão operacionais:

**Inclusão**:
- Diagnóstico de episódio depressivo leve a moderado (PHQ-9 entre 10-19 ou avaliação clínica)
- Ausência de risco suicida iminente (avaliar com Columbia Suicide Severity Rating Scale)
- Capacidade de participar de atividades em grupo (ausência de sintomas psicóticos ativos, agitação grave)
- Comprometimento de participar de pelo menos 10 das 12 sessões

**Exclusão** (com alternativa de cuidado):
- Depressão grave (PHQ-9 ≥ 20): priorizar atendimento individual antes de grupo
- Risco suicida iminente: atendimento individual + avaliação psiquiátrica urgente
- Comorbidade com uso de substâncias ativa: considerar grupo específico ou atendimento paralelo
- Sintomas psicóticos: estabilizar com tratamento medicamentoso antes

**Ação concreta**: Criar ficha de triagem para grupo com critérios operacionalizados.

---

**4. Grupo aberto indefinidamente pode comprometer coesão**

**Problema identificado**: Grupo aberto com entrada/saída constante de participantes dificulta estabelecimento de vínculo, coesão grupal e progressão estruturada de conteúdo.

**Fundamentação**: Metanálise de formatos de grupo terapêutico (Burlingame et al., 2016) indica que grupos fechados com duração definida (8-16 sessões) têm adesão e efetividade superiores a grupos abertos indefinidos, especialmente para protocolos estruturados.

**Recomendação**:
Formato de **grupo fechado com duração definida (12 sessões semanais)**:
- Permite progressão de conteúdo estruturado
- Facilita coesão e confiança entre participantes
- Permite avaliação pré-pós com grupo controle (importante para consolidar prática baseada em evidências local)
- Ofertas regulares de novos grupos (ex: iniciar novo grupo a cada 3 meses)

**Alternativa** (se grupo aberto for obrigatório por demanda):
- Dividir em núcleo fixo (comprometidos com 12 sessões) + participantes flutuantes (máximo 20% das vagas)
- Estruturar sessões como módulos independentes mas progressivos
- Sessão de integração para novos participantes antes de entrada no grupo

**Ação concreta**: Definir formato, divulgar cronograma completo e obter compromisso dos participantes na triagem.

---

**5. Tamanho do grupo pode ser excessivo**

**Problema identificado**: 15 participantes é limite superior para grupo terapêutico, especialmente considerando que depressão frequentemente cursa com inibição social e dificuldade de se expor.

**Fundamentação**: Recomendação de especialistas e diretrizes clínicas indicam 6-10 participantes como ideal para grupos terapêuticos de depressão, permitindo que todos tenham espaço de fala adequado e facilitador consiga manejar dinâmica grupal.

**Recomendação**:
- **Ideal**: 8-10 participantes
- Recrutar 10-12 considerando taxa de abandono de 15-20%
- Se demanda for maior, oferecer múltiplos grupos em paralelo ou sequenciais

**Ação concreta**: Limitar vagas a 10 participantes efetivos, com lista de espera para próximo grupo.

---

**Pontos fortes a manter**:

✓ Iniciativa de criar grupo específico para depressão (alta prevalência, responde bem a grupos)
✓ Frequência semanal adequada para manutenção de vínculo
✓ Duração de sessão (1h30) apropriada para grupos terapêuticos

**Recursos adicionais sugeridos**:

1. **Capacitação**: Se equipe não tem formação em TCC de grupo, considerar supervisão clínica mensal ou curso de curta duração (ex: cursos online FIOCRUZ, capacitações ABP)

2. **Materiais de apoio**: "Mind Over Mood" (Greenberger & Padesky) tem versão em português e pode ser adaptado para grupos; "Vencendo a Depressão" (UFCSPA) tem protocolo gratuito em português

3. **Monitoramento**: Além de PHQ-9, considerar avaliar fatores de processo (coesão grupal com Group Cohesion Scale) para entender mecanismos de mudança

**Referências para aprofundamento**:

- Cuijpers P, et al. Psychotherapy for depression across different age groups: A systematic review and meta-analysis. JAMA Psychiatry. 2020.
- Burlingame GM, et al. Small group treatments: Introduction and application. Psychotherapy Research. 2016.
- Yalom ID, Leszcz M. The Theory and Practice of Group Psychotherapy. 6th ed. 2020.
- Portaria GM/MS 336/2002 (CAPS e modalidades de atendimento).

### Output esperado do agente

O agente forneceria:

1. **Avaliação inicial honesta** sem suavizações excessivas
2. **Feedback estruturado por tópicos** (não em lista única desorganizada)
3. **Fundamentação técnica** com referências científicas
4. **Reconhecimento de pontos fortes** (não apenas críticas)
5. **Recomendações acionáveis** com passos concretos
6. **Alternativas quando pertinente** (não impor única solução)
7. **Recursos para implementação** (materiais, capacitação)
8. **Tom construtivo** que incentiva melhoria sem desmotivar

---

## Padrões transversais aos exemplos

### Densidade narrativa

Todos os outputs evitam:
- ❌ "É de suma importância considerar..."
- ❌ "Na atual conjuntura da saúde mental..."
- ❌ "Faz-se necessário implementar..."

E preferem:
- ✅ Afirmações diretas com fundamentação
- ✅ Verbos ativos e concretos
- ✅ Conexão explícita entre dados e decisões

### Honestidade epistêmica

- Explicita quando dados são insuficientes ("Os dados fornecidos não permitem avaliar X. Recomendo coletar também Y.")
- Reconhece incertezas ("Duas hipóteses plausíveis: A ou B. Sugiro coleta de Z para distinguir.")
- Considera alternativas ("Embora X seja mais comum, no contexto local Y pode ser mais viável.")

### Linguagem destigmatizante

- "Pessoa com transtorno depressivo" (nunca "depressivo")
- "Pessoa em crise" (nunca "em surto")
- "Uso problemático de substâncias" (nunca "viciado")

### Conformidade normativa

- Cita artigos específicos de leis (Lei 10.216/2001, LGPD art. 11-13)
- Referencia portarias por número (Portaria 336/2002, 3.088/2011)
- Menciona resoluções CFM aplicáveis (2.314/2022 para telemedicina)

### Formatação estratégica

- Tabelas para comparações estruturadas
- Negrito em 1-3 conceitos críticos por seção
- Headers descritivos (não apenas "Análise", mas "Análise crítica revela cobertura 70% abaixo do parâmetro nacional")
- Fluxogramas em texto quando possível (ASCII art, Markdown)
