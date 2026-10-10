#!/usr/bin/env bash
set -euo pipefail

# Run from a fresh clone's lean directory with Elan/Lake and Python >= 3.9.
# This portable verifier rebuilds the first question and then the source-derived
# QII dependency closure. It preserves historical verify.sh, whose 4096 MiB cap
# is insufficient for Erdos883SmallCertificate117. The default here is 8192 MiB.
# Mathlib uses its pinned compiled cache; no full Mathlib source rebuild is claimed.

verification_directory="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$verification_directory"
export LEAN_MEMORY_MIB="${LEAN_MEMORY_MIB:-8192}"

python3 - "$@" <<'PY'
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

parser = argparse.ArgumentParser(description="Portable first-question and exact second-question source verification.")
parser.add_argument("--plan", action="store_true", help="Check frozen source manifests and write the QII source topology; compile nothing.")
parser.add_argument("--no-cache-fetch", action="store_true", help="Use already-installed pinned Mathlib dependencies instead of lake exe cache get.")
parser.add_argument("--reuse-first-objects", action="store_true", help="Recheck QII using existing complete first-question build objects; do not claim first sources were rebuilt.")
args = parser.parse_args()
directory = Path.cwd()
memory_mib = int(os.environ["LEAN_MEMORY_MIB"])
if memory_mib <= 0:
    raise SystemExit("LEAN_MEMORY_MIB must be positive.")
expected_lean = "leanprover/lean4:v4.33.1"
expected_lean_commit = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
expected_mathlib = "0df444a360eaa60ab8c11dca51a86af692955474"
standard_axioms = {"propext", "Classical.choice", "Quot.sound"}

def fail(message):
    if "results" in globals() and "save_results" in globals():
        results["status"] = "failed"
        results["failure"] = message
        save_results()
    raise SystemExit(message)

def hash_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()

def mask_comments_and_strings(text):
    output = []
    index = depth = 0
    line_comment = in_string = escaped = False
    while index < len(text):
        char, pair = text[index], text[index:index + 2]
        if line_comment:
            output.append("\n" if char == "\n" else " ")
            line_comment = char != "\n"
            index += 1
        elif depth:
            if pair in ("/-", "-/"):
                depth += 1 if pair == "/-" else -1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif pair in ("--", "/-"):
            line_comment = pair == "--"
            depth = int(pair == "/-")
            output.extend("  ")
            index += 2
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    if depth or in_string:
        fail("Unterminated Lean comment or string.")
    return "".join(output)

if Path("lean-toolchain").read_text().strip() != expected_lean:
    fail("lean-toolchain differs from the pinned Lean version.")
lake_manifest = json.loads(Path("lake-manifest.json").read_text())
mathlib_package = next((entry for entry in lake_manifest["packages"] if entry["name"] == "mathlib"), None)
if mathlib_package is None or mathlib_package["rev"] != expected_mathlib:
    fail("lake-manifest.json differs from the pinned Mathlib revision.")

# Preserve the historical first-question manifest and source hash checks.
first_provenance = json.loads(Path("PROVENANCE.json").read_text())
first_hashes = first_provenance["source_sha256"] | first_provenance["verification_source_sha256"]
for module, expected in first_hashes.items():
    path = Path(module.replace(".", "/") + ".lean")
    if hash_file(path) != expected:
        fail(f"First-question source hash mismatch: {path}")
first_modules = [line.strip() for line in Path("MODULES.txt").read_text().splitlines() if line.strip()]
if len(first_modules) != len(set(first_modules)):
    fail("Duplicate first-question module in MODULES.txt.")
if first_modules != first_provenance["modules"]:
    fail("MODULES.txt differs from the frozen first-question provenance order.")

qii_provenance = json.loads(Path("SECOND_QUESTION_PROVENANCE.json").read_text())
local_sources = {path.stem: path for path in Path(".").glob("Erdos883Second*.lean")}
roots = qii_provenance["roots"]
imports = {}
hashes = {}
states = {}
order = []
external = set()
def visit(module, stack):
    if states.get(module) == 1:
        fail("Local import cycle: " + " -> ".join(stack + [module]))
    if states.get(module) == 2:
        return
    if module not in local_sources:
        fail(f"Missing QII source: {module}.lean")
    states[module] = 1
    path = local_sources[module]
    content = mask_comments_and_strings(path.read_text(encoding="utf-8-sig"))
    if re.search(r"\b(?:sorry|admit|axiom|constant)\b", content):
        fail(f"Proof hole or added axiom/constant declaration in {path}")
    imported_modules = []
    for match in re.finditer(r"(?m)^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)", content):
        for imported in match.group(1).split():
            if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", imported):
                fail(f"Unsupported import syntax in {path}: {imported}")
            imported_modules.append(imported)
    imports[module] = list(dict.fromkeys(imported_modules))
    hashes[module] = hash_file(path)
    for imported in imports[module]:
        if imported.startswith("Erdos883Second"):
            visit(imported, stack + [module])
        else:
            external.add(imported)
    states[module] = 2
    order.append(module)

for root in roots:
    visit(root, [])
if order != qii_provenance["compile_order"]:
    fail("Source-derived QII topology differs from the frozen provenance order.")
if hashes != qii_provenance["source_sha256"]:
    fail("QII source hashes differ from SECOND_QUESTION_PROVENANCE.json.")
if imports != qii_provenance["source_imports"]:
    fail("QII source imports differ from SECOND_QUESTION_PROVENANCE.json.")
if sorted(external) != qii_provenance["external_direct_imports"]:
    fail("QII external imports differ from the frozen provenance.")

plan = {
    "roots": roots,
    "firstQuestionModules": len(first_modules),
    "firstQuestionSourceHashChecks": "matched the original PROVENANCE.json",
    "secondQuestionCompileOrder": order,
    "secondQuestionSourceSha256": hashes,
    "leanToolchain": expected_lean,
    "mathlibRevision": expected_mathlib,
    "leanMemoryMib": memory_mib,
    "firstSourcesWillBeRecompiled": not args.reuse_first_objects,
    "mathlibExplicitBuildTargets": sorted(module for module in external if module.startswith("Mathlib.")),
    "historicalVerifier": "verify.sh is preserved; its first-question source sequence/hash checks are reproduced here with the configurable memory cap",
    "dependencyPolicy": "QII local sources are recompiled. First-question sources are recompiled by default; --reuse-first-objects requires existing objects and records that first sources were not rebuilt. Mathlib uses pinned caches with explicit missing-object builds, rather than a full source rebuild.",
}
Path("SECOND_QUESTION_VERIFICATION_PLAN.json").write_text(json.dumps(plan, indent=2) + "\n")
print(f"Frozen hashes checked; source-derived QII closure: {len(order)} modules.", flush=True)
if args.plan:
    print("Plan only: no dependency download or Lean compilation was performed.", flush=True)
    sys.exit(0)

if not args.no_cache_fetch:
    subprocess.run(["lake", "exe", "cache", "get"], check=True)
actual_mathlib = subprocess.check_output(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], text=True).strip()
if actual_mathlib != expected_mathlib:
    fail("Installed Mathlib checkout differs from the pinned revision.")
mathlib_targets = plan["mathlibExplicitBuildTargets"]
if mathlib_targets:
    # Some Mathlib caches omit the CRT module required by QII. Explicit module
    # targets reuse available cached objects and compile missing dependencies.
    subprocess.run(["lake", "build", *mathlib_targets], check=True)
lean_version = subprocess.check_output(["lake", "env", "lean", "--version"], text=True).strip()
if "version 4.33.1," not in lean_version or expected_lean_commit not in lean_version:
    fail(f"Unexpected Lean executable: {lean_version}")
dependency_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], text=True).strip()
lean_bin = subprocess.check_output(["lake", "env", "which", "lean"], text=True).strip()
environment = os.environ.copy()
environment["LEAN_PATH"] = str(directory) + os.pathsep + dependency_path
stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
log_root = Path("verification-logs") / ("both-questions-" + stamp)
log_root.mkdir(parents=True, exist_ok=False)
results = {"status": "running", "startedAtUtc": datetime.now(timezone.utc).isoformat(), "plan": plan,
    "firstSourcesRecompiled": False, "modules": []}
result_path = Path("SECOND_QUESTION_VERIFICATION_RESULT.json")
def save_results():
    result_path.write_text(json.dumps(results, indent=2) + "\n")
save_results()

def compile_module(module, phase, produce_object=True):
    log_directory = log_root / phase
    log_directory.mkdir(exist_ok=True)
    log_path = log_directory / (module + ".log")
    # As in historical verify.sh, resolve Lake's compiler once and invoke it
    # directly with the explicit local-source plus dependency LEAN_PATH.
    command = [lean_bin, f"-M{memory_mib}"]
    if produce_object:
        command.extend(["-o", module + ".olean"])
    command.append(module + ".lean")
    print(f"{phase}: {module}", flush=True)
    with log_path.open("w") as log:
        process = subprocess.run(command, env=environment, stdout=log, stderr=subprocess.STDOUT)
    text = log_path.read_text(errors="replace")
    axiom_reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    report_map = {name: sorted({item.strip() for item in names.split(",") if item.strip()}) for name, names in axiom_reports}
    unexpected = sorted({axiom for names in report_map.values() for axiom in names} - standard_axioms)
    failed = process.returncode != 0 or re.search(r"\bsorryAx\b|\berror(?:\(|:)", text) or unexpected
    entry = {"phase": phase, "module": module, "returnCode": process.returncode, "log": str(log_path),
        "logSha256": hash_file(log_path), "axiomReports": report_map, "status": "failed" if failed else "passed"}
    results["modules"].append(entry)
    if failed:
        results["status"] = "failed"
        results["failure"] = f"Verification failed at {module}; unexpected axioms: {unexpected}"
        save_results()
        print(text, file=sys.stderr)
        fail(results["failure"])
    if produce_object:
        entry["objectSha256"] = hash_file(Path(module + ".olean"))
    save_results()
    return report_map

# Reproduce verify.sh's unchanged first-question compilation sequence and audit,
# using the corrected configurable cap. Do not reuse precompiled first objects.
if args.reuse_first_objects:
    cached_first = []
    for module in sorted(external):
        if module.startswith(("Mathlib.", "Lean.")):
            continue
        if module not in first_hashes:
            fail(f"External import is not covered by the frozen first-question manifest: {module}")
        object_path = Path(module.replace(".", "/") + ".olean")
        if not object_path.is_file():
            fail(f"--reuse-first-objects requires an existing complete first build; direct dependency object missing: {object_path}")
        cached_first.append({"module": module, "object": str(object_path), "sha256": hash_file(object_path)})
    results["reusedFirstDirectDependencyObjects"] = cached_first
    save_results()
    print("Reusing existing first-question objects; firstSourcesRecompiled=false.", flush=True)
else:
    first_report = None
    for module in first_modules:
        reports = compile_module(module, "first-question")
        if "Erdos883Verified.erdos883_firstQuestion" in reports:
            first_report = reports["Erdos883Verified.erdos883_firstQuestion"]
    compile_module("VERIFY_CANONICAL", "first-question", produce_object=False)
    if first_report is None:
        fail("Missing compiled first-question theorem axiom report.")
    results["firstSourcesRecompiled"] = True
    save_results()

for module in order:
    if hash_file(local_sources[module]) != hashes[module]:
        fail(f"QII source changed during verification: {module}")
    final_reports = compile_module(module, "second-question")
required_reports = {
    "Erdos883Verified.erdos883_firstQuestion",
    "Erdos883Second.secondQuestion",
    "Erdos883Verified.erdos883_secondQuestion_raw",
    "Erdos883Verified.erdos883_bothQuestions",
}
if not required_reports <= set(final_reports):
    fail("Missing exact final theorem axiom reports: " + ", ".join(sorted(required_reports - set(final_reports))))
results["status"] = "passed"
results["finishedAtUtc"] = datetime.now(timezone.utc).isoformat()
save_results()
print("Exact QII local sources verified with standard theorem axioms only.", flush=True)
print("First-question proof sources were " + ("reused as existing compiled objects." if args.reuse_first_objects else "recompiled from source."), flush=True)
print("Mathlib's pinned compiled caches were reused; full Mathlib source rebuild was not performed.", flush=True)
print(f"Result: {result_path}", flush=True)
PY
