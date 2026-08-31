#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"
latexmk \
  -pdf \
  -pvc \
  -view=none \
  -file-line-error \
  -interaction=nonstopmode \
  manuscript.tex
