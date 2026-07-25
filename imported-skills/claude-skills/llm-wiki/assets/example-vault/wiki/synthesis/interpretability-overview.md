---
title: Interpretability Overview
category: synthesis
summary: Current synthesis on mechanistic interpretability in large language models
tags: [interpretability, overview]
sources: 1
updated: 2026-04-10
---

# Interpretability Overview

## Thesis
_(early — only one source ingested)_ Mechanistic interpretability is shifting from direct neuron inspection (limited by polysemanticity) toward sparse-autoencoder-based feature decomposition. The empirical bet is that overcomplete sparse dictionaries recover the "true" feature basis of trained models.

## The landscape
- **Sparse-autoencoder line** — pursued by [[entities/anthropic]]; see [[sources/monosemanticity]]
- **Circuits work** — (no sources ingested yet)
- **Probing** — (no sources ingested yet)

## Key concepts
- [[concepts/sparse-autoencoder]] — primary method under investigation

## Key sources
- [[sources/monosemanticity]] — foundational SAE paper

## Current open problems
- Scaling SAEs beyond toy models
- Whether features are truly monosemantic vs merely "more" monosemantic
- How SAE features relate to circuits-based analysis

## How this synthesis has changed
- **2026-04-10** — initial synthesis after ingesting [[sources/monosemanticity]]. Only one data point; thesis is intentionally tentative.
