#!/usr/bin/env python3
"""Inicializa a estrutura de um vault Zettelkasten (método Luhmann).

Uso: python init_vault.py <caminho-do-vault>

Cria (sem sobrescrever nada que já exista):
  ZettelKasten/
    zettels/     - as notas (teses atômicas conectadas)
    Daily/       - diários e capturas fleeting
    templates/   - templates de nota (permanent, literature, fleeting, moc)
    arquivos/    - imagens e anexos
"""
import os, sys, shutil

TEMPLATES = {
"permanent_notes.md": """---
type: permanent
title:
date:
tags:
  - zettel/permanent
---

# {{title}}

## **Ideia Principal**
(A tese, clara e atômica. Teste: alguém poderia discordar deste título? Se não, ainda é tópico.)

## **Contexto**
(De onde veio: leitura, caso real, conversa. O que provocou a ideia.)

## **Expansão**
(Argumento nas suas palavras. Inclua a melhor objeção contra a própria tese.)

## **Conexões**
- [[Nota existente]] — relação: contradiz | completa | exemplifica | responde
""",
"literature_notes.md": """---
type: literature
title:
source:
author:
date:
tags:
  - zettel/literature
---

# {{title}}

## **Resumo**
(Breve. O resumo é o menos importante desta nota.)

## **Citações Relevantes**
- ""

## **Comentários Pessoais**
(A parte que vale: o que isso significa para as SUAS perguntas — não o que o autor disse.)

## **Conexões**
- [[Nota]] — relação
""",
"fleeting_notes.md": """---
type: fleeting
date:
tags:
  - zettel/fleeting
---

# Fleeting

- **Ideia**: (rápido, sem elaborar — o gancho)
- **Contexto**: (onde surgiu)
- **Processar em**: (qual nota permanente isso pode virar)
""",
"moc_template.md": """---
type: moc
title:
tags:
  - moc
description:
---

# MOC – {{title}}

(Mapa de entrada de um tema. Agrupe notas por subtema e termine com "Pontes a construir":
conexões que o material pede mas ainda não existem.)

## Pontes a construir
-
""",
}

STARTER = """---
type: permanent
title: Uma nota é uma tese, não um tópico
date:
tags:
  - zettel/permanent
---

# Uma nota é uma tese, não um tópico

## **Ideia Principal**
Notas que apenas descrevem um assunto não geram conhecimento novo; notas que afirmam algo contestável criam atrito — e o atrito entre afirmações é de onde a originalidade nasce.

## **Contexto**
Primeira nota deste vault, criada na inicialização. Niklas Luhmann escreveu 70 livros não acumulando conteúdo, mas forçando cada nota nova a entrar numa conversa com as existentes.

## **Expansão**
Teste prático para todo título: dá para discordar dele? "Observabilidade no sistema X" — não dá, é tópico. "Sem telemetria, todo incidente vira arqueologia" — dá, é tese. Objeção honesta: nem tudo precisa ser tese (notas de referência têm valor); o risco é o vault virar SÓ referência.

## **Conexões**
- (esta nota espera sua primeira conexão — crie sua próxima nota e decida a relação entre elas)
"""


TEMPLATES_EN = {
"permanent_notes.md": """---
type: permanent
title:
date:
tags:
  - zettel/permanent
---

# {{title}}

## **Main claim**
(The thesis, clear and atomic. Test: could someone disagree with this title? If not, it is still a topic.)

## **Context**
(Where it came from: a reading, a real case, a conversation. What sparked the idea.)

## **Expansion**
(The argument in your own words. Include the best objection against your own thesis.)

## **Connections**
- [[Existing note]] — relation: contradicts | completes | exemplifies | answers
""",
"literature_notes.md": """---
type: literature
title:
source:
author:
date:
tags:
  - zettel/literature
---

# {{title}}

## **Summary**
(Brief. The summary is the least important part of this note.)

## **Relevant quotes**
- ""

## **Personal commentary**
(The part that matters: what this means for YOUR questions — not what the author said.)

## **Connections**
- [[Note]] — relation
""",
"fleeting_notes.md": """---
type: fleeting
date:
tags:
  - zettel/fleeting
---

# Fleeting

- **Idea**: (quick, unpolished — just the hook)
- **Context**: (where it came up)
- **Process into**: (which permanent note this could become)
""",
"moc_template.md": """---
type: moc
title:
tags:
  - moc
description:
---

# MOC – {{title}}

(Entry map for a theme. Group notes by subtopic and end with "Bridges to build":
connections the material calls for but that do not exist yet.)

## Bridges to build
-
""",
}

STARTER_EN = """---
type: permanent
title: A note is a claim, not a topic
date:
tags:
  - zettel/permanent
---

# A note is a claim, not a topic

## **Main claim**
Notes that merely describe a subject produce no new knowledge; notes that assert something contestable create friction — and friction between claims is where originality comes from.

## **Context**
First note of this vault, created at initialization. Niklas Luhmann wrote 70 books not by hoarding content, but by forcing every new note into a conversation with the existing ones.

## **Expansion**
Practical test for every title: can you disagree with it? "Observability in system X" — you cannot, it is a topic. "Without telemetry, every incident becomes archaeology" — you can, it is a claim. Honest objection: not everything needs to be a claim (reference notes have value); the risk is a vault that is ONLY reference.

## **Connections**
- (this note awaits its first connection — create your next note and decide the relation between them)
"""

STARTER_NAME = {"pt": "Uma nota é uma tese, não um tópico.md", "en": "A note is a claim, not a topic.md"}

def main():
    import argparse
    ap = argparse.ArgumentParser(description="Inicializa a estrutura de um vault Zettelkasten / Initialize a Zettelkasten vault")
    ap.add_argument("path", help="pasta onde criar o vault / folder to create the vault in")
    ap.add_argument("--lang", choices=["pt", "en"], default="pt", help="idioma dos templates / template language (default: pt)")
    args = ap.parse_args()
    templates = TEMPLATES if args.lang == "pt" else TEMPLATES_EN
    starter = STARTER if args.lang == "pt" else STARTER_EN
    base = os.path.join(args.path, "ZettelKasten")
    created, skipped = [], []
    for d in ("zettels", "Daily", "templates", "arquivos"):
        p = os.path.join(base, d)
        (skipped if os.path.exists(p) else created).append(p)
        os.makedirs(p, exist_ok=True)
    for name, content in templates.items():
        p = os.path.join(base, "templates", name)
        if os.path.exists(p): skipped.append(p); continue
        open(p, "w", encoding="utf-8").write(content); created.append(p)
    p = os.path.join(base, "zettels", STARTER_NAME[args.lang])
    if not os.path.exists(p):
        open(p, "w", encoding="utf-8").write(starter); created.append(p)
    print(f"Vault: {base}")
    print(f"Criados/created: {len(created)}")
    for c in created: print(f"  + {c}")
    if skipped: print(f"Já existiam, preservados / already existed, preserved: {len(skipped)}")

if __name__ == "__main__":
    main()
