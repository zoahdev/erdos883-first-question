# Published evidence reference corrections — 10 October 2026

The selected proof remains commit
[`92d8dedf3c2aca876a7e3e141aae874ac5669959`](https://github.com/zoahdev/erdos883-first-question/commit/92d8dedf3c2aca876a7e3e141aae874ac5669959)
(proof A). These subsequent evidence changes correct published log locations and
identify unavailable historical raw logs. They do not select a new proof version.
No Lean source, theorem, recorded result, exit code, timestamp, source/object/log
hash, or axiom assertion has been changed.

The complete proof-A Git tree contains 7,047 entries and is not truncated. It
contains no `AGENTS.md`. The relevant original evidence was downloaded at A;
each downloaded file's bytes were checked against its Git blob ID. The six
original JSON blob IDs and SHA-256 digests are retained in the
[correction manifest](EVIDENCE_LINK_CORRECTIONS_20261010.json).

## Corrections and availability

| Record | Published path corrections | Raw-log references explicitly unavailable |
| --- | ---: | ---: |
| Complete 57-module compilation receipt | 57 | 0 |
| Final independent read-only audit | 1 | 0 |
| First-statement audit | 1 | 0 |
| Near-branch development record | 2 | 0 |
| Signature development record | 16 | 17 |
| Historical spectral development record | 0 | 9 |
| Total | 77 | 26 |

The 57 compilation receipt references originally named an unpublished timestamp
subdirectory. The matching published logs are in `logs/` directly. All 57
published log bytes match the receipt's original `logSha256` values. The frozen
manifest's SHA-256 also matches `manifestSha256` in that receipt.

The final read-only and first-statement logs are published in
`independent-checks/`, and the available near/signature development logs are
published in `../resumed-20261010/`. These references now point to those exact
files. In particular, the original
[`final-readonly-audit-01.log`](independent-checks/final-readonly-audit-01.log)
is available; it was previously referenced from the wrong directory.

The 26 unavailable references identify 23 distinct historical filenames absent
from the complete proof-A tree. Their live `log` fields are now `null`, with the
original reference and an explicit publication-status explanation retained.
Embedded historical output, intermediate failures, reported exit codes and
validation conclusions remain unchanged. No missing historical log has been
reconstructed, rerun, or replaced by a later compilation log for a similarly
named module. These historical raw logs cannot currently be independently
inspected from the published repository. The complete compilation receipt and
its published logs are separate evidence.

## Validation performed

The [offline validation result](EVIDENCE_LINK_CHECK_20261010.json) passed:

- All six original JSON byte hashes match their proof-A Git blobs.
- Corrected JSON differs semantically only in the declared log locations and
  availability metadata.
- All 77 corrected references resolve to published proof-A files.
- All 57 complete-compilation log SHA-256 checks match their original receipts.
- All 23 unavailable historical filenames are absent from the complete proof-A
  tree; 26 individual fields disclose that absence.
- The frozen source-manifest digest still matches the compilation receipt.

The validation used an exact-byte snapshot and the complete proof-A Git tree.
To repeat it in a full Git checkout containing A and these corrected records:

```bash
python3 audit/complete-second-question-20261010/verify-evidence-links.py
```

The [validator](verify-evidence-links.py) uses Python 3.8 or newer and Git. It is
read-only unless an output path is explicitly supplied. It retrieves A's
original evidence from Git and checks the corrected evidence against it.

This correction did not execute Lean, rebuild the first-question or mathlib
closure, conduct new mathematical review, or verify attribution or priority.
The original 57-module run's reuse of pinned standard dependency objects and
earlier first-question objects remains disclosed. Organizer mathematical review,
Lean reproduction, contribution attribution, eligibility and any award decision
remain separate requirements.
