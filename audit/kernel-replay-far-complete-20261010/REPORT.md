# Bounded normal kernel replay of the final second-question module

On 10 October 2026, `leanchecker --verbose Erdos883SecondFarComplete` completed
with exit code **0** for the selected complete-proof source commit `92d8dedf3c2aca876a7e3e141aae874ac5669959`.
This replays the module's new declarations, including `farBranch` and
`secondQuestion`, using Lean's bundled kernel against existing imported
environments. It is a new, limited check of the final module's proof objects.

**Scope:** normal checker mode, not `--fresh`. Imported modules' declarations
were not recursively replayed. This run did not rebuild source files or rerun
the first-question certificates or combined audit. It is not an independent
kernel implementation or organizer verification.

The selected proof commit and its sources remain unchanged. This evidence-only
archive complements the source compilation and axiom reports already published
at the selected commit. It does not change the problem statement, authorship,
historical credits, or the pending award status.

## Inputs and identity

- Lean 4.33.1, compiler commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- mathlib cache commit `0df444a360eaa60ab8c11dca51a86af692955474`.
- Source `lean/Erdos883SecondFarComplete.lean` SHA-256:
  `ee65672899ee594ddd61fafb320f8f62ae0e8f373c90a21de0b9207d03c97af8`.
- Target object SHA-256:
  `41cbacb6c685467a93d083421b7935b2d8420d930495c90654925defcdf3a1b5`.
- [Input identity checks](input-integrity.json) matched the 57 second-question
  and combined-audit source files to Git blobs at the selected commit, their
  existing objects to original compilation receipts, and 39 directly used
  external cached objects to original manifests. These identity checks do not
  themselves constitute compilation or kernel replay of all those modules.

## Run and resources

- Started: `2026-10-10T15:52:04Z`; finished: `2026-10-10T15:52:39Z`.
- Checker wall time reported by inner GNU time: **34.85 seconds**.
- Whole sandbox command wall time: **35.06 seconds**.
- Inner GNU time reported maximum RSS **2,374,716 KiB** (about **2.26 GiB**).
- The shell set an **8 GiB virtual address-space limit** and a **90-second
  deadline**. Read-only input mounts, a cleared environment with explicitly
  supplied runtime variables and a separate
  network namespace were used; the only host directory mounted writable was
  the audit scratch directory. The sandbox also had private `/tmp` and `/dev`.

**RSS guard limitation:** the attempted aggregate `/proc` monitor returned
zero and failed to enforce its intended 1 GiB threshold. That zero is invalid
as a memory measurement. The successful run exceeded 1 GiB according to inner
  GNU time. The runner suppressed its monitor diagnostics; the sandbox did not
  mount `/etc`, needed by the host `/usr/bin/awk` alternatives symlink. The
  outer GNU time's 1,972 KiB reports the sandbox parent and must
not be used as the checker's peak memory. No physical 1 GiB cap is claimed.

## Archived evidence and reproduction

- [Result and hash pins](result.json), [checker output](checker.log),
  [inner resource record](resources.txt), [outer resource record](outer-resources.txt),
  [run log](run.log), and [failed RSS monitor measurements](rss-guard.txt).
- [Path-redacted command script](path-redacted-replay-script.txt) and
  [original inner runner](rss-guard-script.txt). The outer script is an archive:
  substitute the documented local-location placeholders before using it.
  The inner runner is retained to disclose the monitor limitation, not as a
  recommendation to rely on that monitor.
- Only absolute host-location strings were replaced by symbolic placeholders
  in the archived outer script, run log, outer resource record and input-identity
  JSON. The successful
  checker output and inner resource records are unchanged.
- For full source reproduction, use `lean/verify-second-question.sh` and its
  build guide at the selected complete-proof commit. A normal module replay
  requires compatible compiled import objects in `LEAN_PATH`; it does not
  replace that full source build.

The final proof target's mathematics, imported proof environment, contribution
attribution and prize eligibility remain subject to independent organizer
assessment. No acceptance or payment is asserted.
