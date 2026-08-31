#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "Usage: ./paper/publish.sh \"commit message\"" >&2
  exit 2
fi

repo_root="$(git rev-parse --show-toplevel)"
"$repo_root/paper/build.sh"

cd "$repo_root"
git add paper

if git diff --cached --quiet; then
  echo "No paper changes to commit."
  exit 0
fi

git commit -m "$*"
git push
