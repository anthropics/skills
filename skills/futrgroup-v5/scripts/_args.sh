#!/usr/bin/env bash
# _args.sh — shared arg parser sourced by stage scripts
# Sets: WORKDIR BRAND PROVIDER PRODUCT_URL STYLE HOOK SETTING AVATAR MODE DURATION ASPECT

WORKDIR="" BRAND="" PROVIDER="fal+gemini" PRODUCT_URL="" STYLE=""
HOOK="" SETTING="" AVATAR="" MODE="ugc" DURATION=60 ASPECT="9:16"

while [ $# -gt 0 ]; do
  case "$1" in
    --workdir)      WORKDIR="$2"; shift 2 ;;
    --brand)        BRAND="$2"; shift 2 ;;
    --provider)     PROVIDER="$2"; shift 2 ;;
    --product-url)  PRODUCT_URL="$2"; shift 2 ;;
    --style)        STYLE="$2"; shift 2 ;;
    --hook)         HOOK="$2"; shift 2 ;;
    --setting)      SETTING="$2"; shift 2 ;;
    --avatar)       AVATAR="$2"; shift 2 ;;
    --mode)         MODE="$2"; shift 2 ;;
    --duration)     DURATION="$2"; shift 2 ;;
    --aspect)       ASPECT="$2"; shift 2 ;;
    *)              shift ;;   # ignore unknown so stages can share args
  esac
done
