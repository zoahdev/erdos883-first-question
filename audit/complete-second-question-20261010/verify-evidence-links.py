#!/usr/bin/env python3
"""Check evidence paths and original bytes. This does not execute Lean."""
import argparse
import copy
import hashlib
import json
import posixpath
from pathlib import Path
import subprocess

PROOF_A = "92d8dedf3c2aca876a7e3e141aae874ac5669959"
PROOF_TREE = "84ea128d940fc14ecbc07e91b4978a64c83a8e32"
EVIDENCE = "audit/complete-second-question-20261010"

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot-root", type=Path, help="Optional byte-identical original-file snapshot")
    parser.add_argument("--proof-tree", type=Path, help="Full GitHub recursive-tree JSON for snapshot mode")
    parser.add_argument("--patched-root", type=Path, help="Corrected repository tree; defaults to this script's repository")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = (args.patched_root or Path(__file__).resolve().parents[2]).resolve()
    manifest = json.loads((root / EVIDENCE / "EVIDENCE_LINK_CORRECTIONS_20261010.json").read_bytes())
    assert manifest["selectedProofCommit"] == PROOF_A
    assert manifest["selectedProofTree"] == PROOF_TREE
    if args.snapshot_root:
        assert args.proof_tree, "--proof-tree is required with --snapshot-root"
        record = json.loads(args.proof_tree.read_text(encoding="utf-8-sig"))
        assert not record["truncated"]
        # GitHub's trees endpoint may echo the supplied commit ref in sha.
        assert record["sha"] in (PROOF_A, PROOF_TREE)
        assert len(record["tree"]) == manifest["completeProofTreeEntries"]
        tree = {item["path"]: item["sha"] for item in record["tree"] if item["type"] == "blob"}
        def original(path):
            return (args.snapshot_root / path).read_bytes()
    else:
        actual_tree = subprocess.run(["git", "rev-parse", PROOF_A + "^{tree}"], cwd=root,
                                     check=True, capture_output=True, text=True).stdout.strip()
        assert actual_tree == PROOF_TREE
        result = subprocess.run(["git", "ls-tree", "-r", PROOF_A], cwd=root, check=True, capture_output=True)
        tree = {}
        for line in result.stdout.decode().splitlines():
            metadata, path = line.split("\t", 1)
            if metadata.split()[1] == "blob":
                tree[path] = metadata.split()[2]
        def original(path):
            return subprocess.run(["git", "show", PROOF_A + ":" + path], cwd=root,
                                  check=True, capture_output=True).stdout

    def get_parent(value, pointer):
        parts = pointer.lstrip("/").split("/")
        for part in parts[:-1]:
            value = value[int(part)] if isinstance(value, list) else value[part]
        return value, parts[-1]

    checked_files = []
    published = 0
    missing = 0
    for item in manifest["originalFiles"]:
        path = item["path"]
        data = original(path)
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        assert blob == tree[path] == item["git_blob_sha1"], path
        assert hashlib.sha256(data).hexdigest() == item["sha256"], path
        before = json.loads(data)
        expected = copy.deepcopy(before)
        for change in [change for change in manifest["changes"] if change["file"] == path]:
            container, key = get_parent(expected, change["pointer"])
            assert container[key] == change["original_reference"]
            if change["corrected_reference"] is None:
                filename = posixpath.basename(change["original_reference"])
                assert not any(posixpath.basename(path) == filename for path in tree), filename
                container[key] = None
                container[key + "_original_reference"] = change["original_reference"]
                container[key + "_publication_status"] = (
                    "Raw log not published in selected proof commit " + PROOF_A +
                    "; preserved historical result is not independently checkable from this raw log.")
                missing += 1
            else:
                log_path = posixpath.normpath(posixpath.join(posixpath.dirname(path), change["corrected_reference"]))
                assert log_path == change["proof_a_path"]
                assert tree[log_path] == change["git_blob_sha1"]
                log_bytes = original(log_path)
                assert hashlib.sha256(log_bytes).hexdigest() == change["sha256"]
                container[key] = change["corrected_reference"]
                published += 1
        corrected = json.loads((root / path).read_bytes())
        assert corrected == expected, "Unexpected semantic edit: " + path
        checked_files.append({"path": path, "original_git_blob_sha1": blob,
                              "original_sha256": item["sha256"],
                              "corrected_sha256": hashlib.sha256((root / path).read_bytes()).hexdigest(),
                              "only_declared_path_and_availability_edits": True})

    receipt = json.loads((root / EVIDENCE / "complete-second-question-verification.json").read_bytes())
    assert len(receipt["modules"]) == 57
    for module in receipt["modules"]:
        log_path = posixpath.normpath(posixpath.join(EVIDENCE, module["log"]))
        assert hashlib.sha256(original(log_path)).hexdigest() == module["logSha256"]
    recorded_manifest = original(EVIDENCE + "/complete-second-question-manifest.json")
    manifest_match = hashlib.sha256(recorded_manifest).hexdigest() == receipt["manifestSha256"]
    assert manifest_match, "The published source manifest does not match the compilation receipt."
    result = {"status": "passed", "selectedProofCommit": PROOF_A, "selectedProofTree": PROOF_TREE,
              "checkedOriginalJsonFiles": len(checked_files), "correctedPublishedLogReferences": published,
              "explicitlyUnavailableHistoricalLogReferences": missing,
              "uniqueUnavailableRawLogs": len({change["original_reference"] for change in manifest["changes"]
                                               if change["corrected_reference"] is None}),
              "closureLogSha256Checks": 57, "recordedManifestDigestMatchesPublishedBytes": manifest_match,
              "fileIntegrityChecks": checked_files,
              "scope": "Offline original-byte, path and evidence-metadata audit only; no Lean execution, proof verification, mathematical review or award acceptance."}
    serialized = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_bytes(serialized.encode("utf-8"))
    print(serialized)

if __name__ == "__main__":
    main()
