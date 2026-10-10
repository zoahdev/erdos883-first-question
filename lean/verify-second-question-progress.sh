#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake_lean_path="$(lake env printenv LEAN_PATH)"
export LEAN_PATH=".:$lake_lean_path"
lean_bin="$(lake env which lean)"
mkdir -p verification-logs/second-question-progress
modules=(
  Erdos883SecondQuestion
  Erdos883SecondQuestionFinsets
  Erdos883SecondQuestionOne
  Erdos883SecondQuestionOneVerified
  Erdos883SecondPrimeSupport
  Erdos883SecondMoment
  Erdos883SecondMomentBound
  Erdos883SecondCounts
  Erdos883SecondGoodProfiles
)
for mod in "${modules[@]}"; do
  "$lean_bin" -M4096 -o "$mod.olean" "$mod.lean" \
    > "verification-logs/second-question-progress/$mod.log" 2>&1
  if grep -q 'sorryAx\|declaration uses .sorry.' "verification-logs/second-question-progress/$mod.log"; then
    cat "verification-logs/second-question-progress/$mod.log" >&2
    exit 1
  fi
  cat "verification-logs/second-question-progress/$mod.log"
done
printf '%s\n' 'Partial development checked. No full SecondQuestion theorem is proved by this script.'
