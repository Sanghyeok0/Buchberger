#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"
latexmk \
  -pdf \
  -file-line-error \
  -halt-on-error \
  -interaction=nonstopmode \
  manuscript.tex

printf '\nBuilt %s/manuscript.pdf\n' "$PWD"
