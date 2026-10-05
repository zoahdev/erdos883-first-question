#!/bin/sh
set -eu
cd "$(dirname "$0")"
for doc in manuscript reproduction_guide contribution_comparison; do
  xelatex -no-shell-escape -interaction=nonstopmode -halt-on-error "$doc.tex"
  xelatex -no-shell-escape -interaction=nonstopmode -halt-on-error "$doc.tex"
done
