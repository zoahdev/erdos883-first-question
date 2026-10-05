#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean_bin="$(lake env which lean)"
lake_lean_path="$(lake env printenv LEAN_PATH)"
export LEAN_PATH=".:$lake_lean_path"
mkdir -p verification-logs
python3 - <<'PY_VERIFY_SOURCES'
import hashlib,json
from pathlib import Path
manifest=json.loads(Path('PROVENANCE.json').read_text())
for module,expected in (manifest['source_sha256'] | manifest['verification_source_sha256']).items():
    path=Path(module.replace('.', '/')+'.lean')
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected: raise SystemExit(f'Source hash mismatch: {path}')
print('All source hashes match the frozen manifest.')
PY_VERIFY_SOURCES
while IFS= read -r mod; do
  printf 'Checking %s\n' "$mod"
  runner=()
  if command -v flock >/dev/null 2>&1; then runner=(flock lean-build.lock); fi
  if ! "${runner[@]}" "$lean_bin" -M4096 -o "$mod.olean" "$mod.lean" > "verification-logs/$mod.log" 2>&1; then
    cat "verification-logs/$mod.log" >&2; exit 1
  fi
  if grep -q 'sorryAx' "verification-logs/$mod.log"; then exit 1; fi
done < MODULES.txt
"${runner[@]}" "$lean_bin" -M4096 VERIFY_CANONICAL.lean > verification-logs/VERIFY_CANONICAL.log 2>&1
cat verification-logs/Erdos883VerifiedCoverage.log
python3 - <<'PY_VERIFY_AXIOMS'
import re
from pathlib import Path
log=Path('verification-logs/Erdos883VerifiedCoverage.log').read_text()
match=re.search(r"'Erdos883Verified.erdos883_firstQuestion' depends on axioms: \[([^\]]*)\]", log)
if match is None: raise SystemExit('Missing final theorem axiom report.')
actual={x.strip() for x in match[1].split(',') if x.strip()}
if not actual <= {'propext','Classical.choice','Quot.sound'}:
    raise SystemExit(f'Unexpected final axioms: {actual}')
print('Canonical first-question theorem compiled with standard axioms only.')
PY_VERIFY_AXIOMS
