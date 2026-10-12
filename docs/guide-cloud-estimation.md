# Guide d'utilisation de Cloud Estimation

Ce guide accompagne la [suite et ses bundles](../skill-updates/2026-10-07/cloud-estimation-suite/README.md).
Consultez aussi le [guide anglais](cloud-estimation-guide.md).

## Pourquoi utiliser la suite

La suite transforme un besoin cloud en classeur de décision traçable : chaque
charge, coût et choix renvoie à une source, une hypothèse ou un arbitrage.
Un montant global sans périmètre ni justification ne permet pas de comparer des
options, de déduire le travail déjà réalisé ou de faire valider les inconnues.
Ces onze skills apportent un même cadre, utilisable pour un domaine isolé ou
pour consolider infrastructure, sécurité, livraison et exploitation.

## Ce que la suite produit

Le livrable principal obligatoire est un `.xlsx` éditable et recalculé, accompagné
du modèle `EstimateModel` et des preuves de validation. Il conserve les sources
datées, hypothèses, risques, arbitrages, critères d'acceptation et un diagramme
cohérent avec l'inventaire. Le Build ponctuel s'exprime en JH (jour-homme), le
Run humain récurrent en JH/month ; coûts cloud et autres OPEX restent séparés.
Les montants sont en EUR, avec TJM et conversion de devise explicités. La
convention de huit heures par JH est une hypothèse éditable ; charge et durée
calendaire sont deux grandeurs distinctes.

Les scénarios `Economique`, `Standard` et `Resilient` conservent le même périmètre
de service. Une option alternative ne s'ajoute pas à une autre dans un budget.
Un prix inconnu reste « à chiffrer » et rend les totaux concernés incomplets.
Une section sans objet porte `Non applicable` et sa raison ; aucun onglet n'est
supprimé. Les douze onglets sont décrits dans « Lire et contrôler le XLSX ».
Le [contrat d'entrée commun](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/references/intake.md)
précise le modèle et les interfaces de génération.

## Choisir le bon skill

Commencez par `cloud-estimation-orchestrator` dès que deux domaines se recouvrent
ou que des estimations doivent être réconciliées. Pour un besoin limité à un
domaine, appelez directement le spécialiste. Les liens ouvrent ses instructions
complètes ; les entrées ci-dessous sont le minimum pour démarrer, à compléter
selon les inconnues qui changent le résultat.

| Skill | Utiliser quand | Pourquoi | Entrées minimales | Résultat distinctif |
|---|---|---|---|---|
| [`cloud-estimation-orchestrator`](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/SKILL.md) | Plusieurs domaines ou estimations existantes | Éviter les doublons et contradictions | Périmètre, inventaire, estimations, sources, contraintes | Un modèle consolidé avec un propriétaire par tâche |
| [`infra-work-estimator`](../skill-updates/2026-10-07/cloud-estimation-suite/infra-work-estimator/SKILL.md) | Travaux d'infrastructure | Chiffrer le travail restant | Environnements, état actuel/cible, réseaux, services, couverture existante | JH bruts, couverts et nets avec dépendances |
| [`cloud-architecture-advisor`](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-architecture-advisor/SKILL.md) | Choix d'hébergement | Comparer pertinence et responsabilité opérationnelle | Charge, croissance, disponibilité, RTO/RPO, équipe | Décision d'architecture et alternatives rejetées |
| [`kubernetes-architect`](../skill-updates/2026-10-07/cloud-estimation-suite/kubernetes-architect/SKILL.md) | Pertinence ou conception Kubernetes | Rendre explicite la charge de plateforme | Besoins de cluster, charge, isolation, équipe, reprise | Justification de Kubernetes ou `Non applicable` |
| [`cicd-devsecops-estimator`](../skill-updates/2026-10-07/cloud-estimation-suite/cicd-devsecops-estimator/SKILL.md) | Chaîne de build et livraison | Chiffrer promotion, contrôles et rollback | Dépôts, pipeline existant, environnements, runners, contrôles | Tâches et preuves de livraison sécurisée |
| [`server-hardening-estimator`](../skill-updates/2026-10-07/cloud-estimation-suite/server-hardening-estimator/SKILL.md) | Sécurité des hôtes | Identifier les contrôles et leur maintien | Inventaire, OS, exposition, accès, patching, sauvegardes | Baseline de durcissement et preuves de restauration |
| [`hosting-capacity-simulator`](../skill-updates/2026-10-07/cloud-estimation-suite/hosting-capacity-simulator/SKILL.md) | Dimensionnement ou surcharge | Distinguer mesures et hypothèses | Charge/pics, CPU, mémoire, stockage, IOPS, débit, concurrence | Sensibilités, plafonds et réserve après panne |
| [`cloud-provider-selector`](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-provider-selector/SKILL.md) | Comparaison de fournisseurs | Comparer des services admissibles à périmètre égal | Architecture, régions, critères, prix datés, horizon | Scores justifiés et TCO sur trois ans |
| [`finops-optimizer`](../skill-updates/2026-10-07/cloud-estimation-suite/finops-optimizer/SKILL.md) | Optimisation d'une plateforme existante | Étayer économies et réversibilité | Facturation autorisée, métriques, période, couverture, pics | Économies prévisionnelles ou mesurées, effort et retour |
| [`cloud-migration-estimator`](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-migration-estimator/SKILL.md) | Transition source vers cible | Couvrir intégrité, bascule et retour arrière | Inventaire source/cible, volumes, dépendances, fenêtre, RTO/RPO | Phases, répétition, cutover, rollback et hypercare |
| [`cloud-architecture-diagrammer`](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-architecture-diagrammer/SKILL.md) | Inventaire et flux à représenter | Garder diagramme et classeur cohérents | IDs des composants, environnements, flux prouvés, inconnues | Diagramme intégré avec registre des composants et flux |

## Installation

Depuis les [bundles distribués](../skill-updates/2026-10-07/cloud-estimation-suite/bundles/),
inspectez le [manifest et ses hashes SHA-256](../skill-updates/2026-10-07/cloud-estimation-suite/bundles/manifest.json).
Chaque fichier `.skill` est une archive compatible ZIP : extrayez le dossier
complet du skill, en conservant `SKILL.md`, références, scripts, assets, licence
et manifest de membres ensemble.

Pour Codex, utilisez `$CODEX_HOME/skills` ou le répertoire de skills configuré.
Pour Claude Code, utilisez `~/.claude/skills`. Installez dans une destination
absente ; si un skill y existe déjà, examinez son contenu et ses modifications
avant tout remplacement. Vérifiez ensuite que l'assistant découvre le nom exact
du skill dans votre session. Le dossier d'auteur du dépôt n'est pas requis à
l'exécution : les bundles sont autonomes.

Le runtime public nécessite Python 3.11+, openpyxl et Pillow. Excel COM sous
Windows ou LibreOffice fournit le recalcul natif. Voir les commandes et limites
dans [Regenerate and validate](../skill-updates/2026-10-07/cloud-estimation-suite/README.md#regenerate-and-validate).
L'installation ne donne aucune autorisation de modifier un compte cloud.

## Préparer le brief

Préparez ce qui est disponible et marquez le reste comme inconnu :

- Périmètre : applications/services inclus, exclusions, état actuel et cible,
  responsables, échéance, estimations existantes et travail déjà couvert.
- Environnements : développement, staging, production, régions admissibles et
  inventaire identifié ; état déployé, partiel, prévu ou inconnu de chaque composant.
- Charge : mesures datées, pics, croissance, volumes, concurrence et saturation.
- Disponibilité : SLO, RTO/RPO (objectifs de reprise et de perte de données),
  sauvegardes, restauration et preuves disponibles.
- Sécurité : exposition, accès, conformité, contrôles hôtes et responsabilités.
- Pipeline : dépôts, build/tests, runners, promotion, rollback et contrôles existants.
- Coûts : exports de facturation autorisés, SKU/région/unité, devise, TJM,
  tarifs datés, taxes/remises et horizon de comparaison explicités.
- Contraintes : capacité disponible en JH par période et rôle, compétences,
  calendrier, dépendances et contraintes commerciales ou de localisation.
- Sources : document/URL, date, propriétaire, confiance, contradictions et
  distinction entre valeurs mesurées, estimées et supposées.

Sans mesures nécessaires, demandez un instrument de collecte en lecture seule
et une tâche préalable bloquante. Gardez les documents privés hors des exemples
publics. Le [contrat d'intake](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/references/intake.md)
décrit le traitement des données manquantes.

## Parcours standard

1. Router : sélectionner le spécialiste, ou l'orchestrateur pour plusieurs
   domaines ; fixer périmètre, exclusions et propriétaires.
2. Collecter : établir inventaire, sources datées et mesures ; qualifier les
   inconnues et contradictions avant de chiffrer.
3. Modéliser : préparer tâches nettes, dépendances, scénarios comparables,
   coûts séparés, capacité par période et décisions ; réconcilier les doublons.
4. Générer : dessiner uniquement les composants et flux étayés, puis produire
   le modèle et les douze onglets du `.xlsx` avec formules et entrées éditables.
5. Recalculer/valider : recalculer et rouvrir le fichier, vérifier caches,
   totaux, scénarios et diagramme ; fournir preuves et moteur utilisé.
6. Approuver : faire examiner inconnues, risques, arbitrages et critères
   d'acceptation par les responsables. Un gate requis non évalué ou échoué
   maintient le classeur en brouillon. L'approbation de l'estimation ne déploie rien.

## Prompts copiables

Remplacez les champs entre crochets par votre brief. Chaque spécialiste conserve
le contrat commun : `.xlsx` éditable, Build en JH, Run humain en JH/month, coûts
séparés, sources datées, hypothèses, risques et inconnues « à chiffrer ».

### Consolidation

```text
Utilise `cloud-estimation-orchestrator` pour produire un chiffrage consolidé.
Périmètre : [applications, environnements et services inclus].
Données disponibles : [inventaire, charge, SLO/RTO/RPO, pipeline, sécurité].
Données inconnues : [prix, éligibilité régionale, capacité mesurée].
Compare : [scénarios de même périmètre].
Exprime le Build en JH, le Run humain en JH/month et sépare les coûts cloud.
Le livrable obligatoire est un `.xlsx` éditable avec sources datées,
hypothèses, risques, arbitrages, critères d'acceptation et diagramme.
N'invente aucun prix, service disponible, flux ou topologie : conserve les
inconnues comme « à chiffrer » ou comme décisions bloquantes.
```

### Infrastructure

```text
Utilise `infra-work-estimator` pour [périmètre et environnements].
Voici l'inventaire actuel/cible et les preuves du travail couvert : [sources].
Estime les JH bruts, couverts et nets, dépendances, rôles et critères d'acceptation.
Compare la charge nette à [capacité par période]. Livre le `.xlsx` commun.
```

### Architecture

```text
Utilise `cloud-architecture-advisor` pour comparer [options d'hébergement].
Garde [charge, environnements, croissance et RTO/RPO] identiques entre options.
Documente critères, responsabilités opérateur, décisions et alternatives rejetées.
Livre le `.xlsx` commun avec Build, Run humain et OPEX séparés.
```

### Kubernetes

```text
Utilise `kubernetes-architect` pour évaluer [besoins, charge, isolation et équipe].
Justifie la pertinence face à [option plus simple] avant de concevoir le cluster.
Si pertinent, chiffre plateforme, exploitation et reprise ; sinon explique
`Non applicable`. Livre le `.xlsx` commun et les preuves manquantes.
```

### CI/CD et DevSecOps

```text
Utilise `cicd-devsecops-estimator` pour [dépôts, pipeline et environnements].
Voici l'existant vérifié : [build, tests, runners, promotion, contrôles].
Chiffre uniquement le travail restant, rollback et Run ; indique les preuves
d'acceptation et les dépendances. Livre le `.xlsx` commun.
```

### Durcissement des serveurs

```text
Utilise `server-hardening-estimator` pour [hôtes, OS, exposition et accès].
Évalue [baseline, patching, sauvegardes, restauration et conformité].
Distingue contrôles prouvés et travail restant, Build et maintien récurrent.
Livre le `.xlsx` commun avec preuves et exclusions de sécurité applicative.
```

### Capacité

```text
Utilise `hosting-capacity-simulator` avec [mesures, période, pics et croissance].
Teste CPU, mémoire, stockage, IOPS, débit et concurrence sur [topologie prouvée].
Expose saturation, plafonds et capacité après panne sans confondre hypothèses
et benchmarks. Livre le `.xlsx` commun ; bloque les mesures manquantes.
```

### Fournisseurs

```text
Utilise `cloud-provider-selector` pour [architecture et fournisseurs candidats].
Vérifie [régions, services, contraintes] et utilise [prix officiels datés].
Compare critères pondérés, Build, Run, cloud/autres OPEX et TCO sur trois ans
à périmètre égal dans le `.xlsx` commun. Garde les prix inconnus « à chiffrer ».
```

### FinOps

```text
Utilise `finops-optimizer` avec [export de facturation autorisé et métriques].
Période, couverture, pics et saisonnalité : [détails]. Réconcilie la baseline.
Distingue économies prévues/mesurées, coûts déplacés, Build, Run additionnel,
bénéfice net et retour ; évite les gains en double. Livre le `.xlsx` commun
avec mesures avant/après comparables et rollback pour chaque action.
```

### Migration

```text
Utilise `cloud-migration-estimator` pour [source, cible, volumes et dépendances].
Contraintes : [fenêtre de bascule, RTO/RPO, intégrité et responsables].
Chiffre préparation, transfert, répétition, cutover, rollback et hypercare.
Livre le `.xlsx` commun ; laisse les accès, débits et prix inconnus bloquants.
```

### Diagramme

```text
Utilise `cloud-architecture-diagrammer` avec [inventaire identifié et flux prouvés].
Représente [environnements et zones documentés] sans inventer de connexions.
Consigne les inconnues, utilise des symboles neutres et vérifie les IDs.
Intègre le rendu final au `.xlsx` commun avec son registre de composants/flux.
```

## Exemples de bout en bout

Ces trois demandes utilisent des champs à remplir, sans données client ni prix
inventés. La [démonstration synthétique](../skill-updates/2026-10-07/cloud-estimation-suite/README.md#workbook-and-synthetic-example)
montre un classeur complet, mais ses tarifs et sa capacité ne sont pas des devis
ou mesures réutilisables.

### A — Infrastructure, pipeline, sécurité et fournisseurs

Préparez inventaire, état actuel/cible, couverture existante, pipeline, baseline
hôtes, charge, objectifs de reprise, sources tarifaires et disponibilité de l'équipe.
L'orchestrateur route vers infrastructure, CI/CD, durcissement et sélection de
fournisseur, puis fusionne les tâches avec un propriétaire unique.

```text
Utilise `cloud-estimation-orchestrator` pour [applications et environnements].
Mobilise `infra-work-estimator`, `cicd-devsecops-estimator`,
`server-hardening-estimator` et `cloud-provider-selector` selon le périmètre.
Entrées : [inventaire, existant prouvé, pipeline, sécurité, charge, RTO/RPO,
équipe et sources tarifaires datées]. Réconcilie couverture et doublons.
Livre un `.xlsx` consolidé avec Build net JH, Run JH/month, coûts séparés,
diagramme et preuves. Les prix inconnus restent « à chiffrer ».
```

À réception, contrôlez `04_Taches_JH` pour les doublons et critères d'acceptation,
`07_Phasage` pour les dépendances/surcharges, puis les scénarios et sources.
Faites valider les décisions encore ouvertes avant l'approbation.

### B — FinOps sur une plateforme existante

Appelez directement le spécialiste avec export autorisé réconcilié, périmètre,
période et métriques couvrant pics et saisonnalité. Des métriques seules ne
constituent pas une facture mesurée.

```text
Utilise `finops-optimizer` sur [plateforme existante].
Entrées : [export de facturation autorisé, totaux de contrôle, métriques,
période, couverture, pics et saisonnalité]. Propose des actions réversibles.
Livre un `.xlsx` distinguant économies prévisionnelles et validées par mesure,
gains bruts, coûts déplacés, Build JH, Run JH/month et bénéfice net.
Si des prix manquent, indique « à chiffrer » et des totaux incomplets,
sans annoncer zéro économie ou un retour sur investissement complet.
```

Relisez baseline dans `01_Hypotheses`, actions dans `04_Taches_JH`, justification
dans `09_Arbitrages` et preuves dans `10_Sources`. Un gain reste prévisionnel
jusqu'à une mise en œuvre autorisée et une mesure après changement comparable.
Le [catalogue d'optimisation](../skill-updates/2026-10-07/cloud-estimation-suite/finops-optimizer/references/optimisation-catalogue.md)
précise les contrôles par action.

### C — Kubernetes, runtime managé ou VPS, puis fournisseur

Préparez charge, croissance, environnements, objectifs de reprise, compétences et
contraintes d'éligibilité identiques. Choisissez d'abord l'architecture, puis
comparez les fournisseurs sur ses exigences ; gardez les alternatives exclusives.

```text
Utilise `cloud-estimation-orchestrator` pour comparer Kubernetes, runtime managé
et VPS sur [même charge, environnements, horizon, RTO/RPO et contraintes].
Utilise `cloud-architecture-advisor` et `kubernetes-architect` pour justifier
la pertinence, les responsabilités et les alternatives rejetées, puis
`cloud-provider-selector` pour comparer éligibilité, prix datés et TCO sur trois ans.
Livre un `.xlsx` avec décision, Build JH, Run JH/month et OPEX séparés.
Ne somme pas les options ; distingue les variantes Economique/Standard/Resilient.
Si prix ou éligibilité manquent, conserve « à chiffrer » et le choix provisoire.
```

Relisez l'ADR (décision d'architecture) dans `09_Arbitrages`, la comparaison dans
`06_Scenarios` et la synthèse dans `11_Synthese`. Vérifiez les critères et raisons
de rejet avec la [matrice de décision](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-architecture-advisor/references/decision-matrix.md),
la [checklist Kubernetes](../skill-updates/2026-10-07/cloud-estimation-suite/kubernetes-architect/references/cluster-checklist.md)
et les [règles de scoring fournisseur](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-provider-selector/references/scoring.md).
Ajoutez capacité, sécurité ou livraison seulement si le périmètre le nécessite.

## Lire et contrôler le XLSX

| Onglet | À examiner |
|---|---|
| `00_Lisez-moi` | Périmètre, mode d'emploi, unités et limites |
| `01_Hypotheses` | Entrées éditables, statut, TJM et conversions |
| `02_Inventaire` | Composants identifiés, quantités et environnements |
| `03_Architecture` | Diagramme final et cohérence des composants/flux |
| `04_Taches_JH` | JH bas/probable/haut, propriétaires, dépendances et acceptation |
| `05_Couts_cloud` | Services, quantités, prix sourcés et coûts récurrents |
| `06_Scenarios` | Alternatives comparables et sélection par formules |
| `07_Phasage` | Phases, jalons, dépendances et capacité disponible |
| `08_Risques` | Impacts, mesures de réduction et responsables |
| `09_Arbitrages` | Questions, options, raisons et décisions ouvertes |
| `10_Sources` | Provenance, date, URL et confiance |
| `11_Synthese` | Totaux réconciliés et limites de décision |

Convention : entrées en texte bleu, formules en noir, formules inter-onglets
en vert et hypothèses éditables importantes sur fond jaune. Vérifiez le statut
des valeurs autant que leur couleur. Les totaux doivent correspondre au détail,
au phasage et au scénario sélectionné, sans additionner alternatives ou Build et
Run. Vérifiez les prix absents, tâches couvertes et inconnues de reprise.

Demandez le moteur de recalcul, les comptes de formules/caches et les résultats
positifs des contrôles : erreurs de formule, écarts de rapprochement et delta
d'inventaire nuls. L'ouverture native et la validation des caches sont deux
preuves distinctes. Ne sauvegardez jamais via openpyxl un classeur chargé avec
`data_only=True` : les formules seraient perdues. Les contrôles détaillés restent
dans le [gate de livraison](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/SKILL.md#pre-delivery-gate).

## Limites et sécurité

Un chiffrage n'est ni un devis fournisseur, ni un benchmark, ni une certification
de sécurité ou de reprise. Une réserve de capacité ne prouve pas une reprise
inter-zone/région. Vérifiez tarifs, services/SKU, disponibilité régionale et
conditions commerciales aux sources officielles datées ou exports autorisés.
N'inventez aucun flux, prix ou service ; exposez les inconnues et impacts.

Les skills ne donnent aucune autorisation de déployer, migrer, changer des
droits, supprimer des ressources, acheter un engagement ou lancer des agents.
Le routage sélectionne des instructions ; chaque action reste soumise à la
portée autorisée par l'utilisateur. Une décision d'estimation n'autorise pas
son exécution opérationnelle.

Gardez sources privées, secrets, identifiants de compte/projet, chemins internes,
devis réels et topologie client hors des bundles et exemples publics. Utilisez
des données synthétiques pour une démonstration ; un scan sans correspondance
ne prouve pas à lui seul l'anonymat. Les détails figurent dans la
[politique de données publiques](../skill-updates/2026-10-07/cloud-estimation-suite/README.md#icon-and-public-data-policy).

## Dépannage

- Skill introuvable : vérifiez le répertoire configuré, le nom exact et la
  présence de `nom-du-skill/SKILL.md` après extraction. Vérifiez le manifest du
  bundle ; évitez un dossier imbriqué supplémentaire. Recontrôlez la découverte
  dans la session de l'assistant après installation.
- Dépendances absentes : vérifiez que Python 3.11+, openpyxl et Pillow sont
  disponibles dans l'environnement qui exécute le runtime. pytest et PyYAML
  servent aux tests d'auteur. Suivez les commandes du README de la suite.
- Recalcul natif indisponible : vérifiez Excel COM sous Windows ou LibreOffice.
  `--require-native` doit échouer si aucun moteur natif ne recalcule et sauvegarde.
  Le repli Python calibré doit être déclaré ; ses opérations limitées ne prouvent
  pas une ouverture native et ne satisfont pas un gate qui l'exige.
- Prix, TJM ou éligibilité inconnus : demandez la source ou consignez une décision
  bloquante et « à chiffrer ». Ne remplacez pas un prix absent par zéro. Dans le
  modèle numérique, gardez le composant en inventaire et l'inconnue dans les
  hypothèses/risques/arbitrages ; omettez la ligne tarifée et signalez les totaux
  incomplets selon le contrat d'intake. Distinguez charge JH connue et finance
  non validée ; demandez les preuves requises avant approbation.
