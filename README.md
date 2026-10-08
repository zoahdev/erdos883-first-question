# Erdős Problem 883: first-question all-n proof — Yicheng Pan (潘奕成, zoahdev)

**The first question is proved for every natural number n.** This repository
contains the unchanged Lean proof source, the aligned manuscript, and a
separate independent rebuild audit. The second question is outside this contribution.

Author: **Yicheng Pan (潘奕成), GitHub: zoahdev**.

[English / 中文 author and contribution summary](https://zoahdev.github.io/erdos-883/) · [Public proof claim](https://www.erdosproblems.com/forum/thread/883/proof-claims)

中文：潘奕成（zoahdev）在 Donald Della Pietra 的渐近工作基础上完成埃尔德什第 883 题第一问的全 n 证明与 Lean 形式化；第二问不属于此贡献。

GitHub: [zoahdev](https://github.com/zoahdev). Erdős Problems account:
[yichengpan](https://www.erdosproblems.com/forum/user/yichengpan).
These are Yicheng Pan's public accounts for this contribution.

- [Manuscript (PDF)](paper/Erdos883_Lean_Aligned_Manuscript_20261005.pdf)
- [Lean proof and original reproduction instructions](lean/README.md)
- [Reproduction guide (PDF)](paper/Erdos883_Reproduction_Guide_20261005.pdf)
- [Contribution and prior-work comparison (PDF)](paper/Erdos883_Contribution_Comparison_20261005.pdf)
- [Independent rebuild summary](audit/KERNEL_RECHECK.json)
- [Canonical statement and axiom audit](audit/VERIFY_CANONICAL_REPLAY.log)
- [Per-module rebuild receipt](audit/MODULE_KERNEL_REPLAY_RECEIPT.json)
- [Reproduction errata](REPRODUCTION_ERRATA.txt)

## Exact scope

For every natural n and every A ⊆ {1,...,n} with
|A| > floor(n/2) + floor(n/3) - floor(n/6), the induced coprime graph on A
contains a genuine cycle of every odd length l satisfying 3 ≤ l ≤ floor(n/3)+1.

The final theorem is `Erdos883Verified.erdos883_firstQuestion` in
`lean/Erdos883VerifiedCoverage.lean`. The proof covers n < 200000 with finite
certificates and n ≥ 200000 with the formalized analytic argument.

## Independent source rebuild

All **6,831 local modules** were compiled afresh from the frozen source with
Lean **4.33.1** and the pinned dependency revisions. No supplied local proof
objects were reused; standard dependencies used the pinned official Mathlib
cache. The canonical raw-statement harness passed. The final theorem's only
axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The rebuilt final `.olean` SHA256 matches the submitted final-object record.
No proof source was changed during the independent rebuild.

The manuscript's audit description predates this independent rebuild. Its
previously pending clean replay is now documented in the separate `audit/`
records; the manuscript and original historical records have been preserved.

The original `verify.sh` uses a 4096 MiB cap. One unchanged module,
`Erdos883SmallCertificate117`, exceeded that cap and passed alone with an
8192 MiB cap. Reproduction also requires Python ≥ 3.9. See the errata and
audit receipt for the exact settings and two original documentation defects.
The original source and historical records are preserved separately from
the new audit, rather than rewritten to suggest the original script passed unchanged.

## Attribution and disclosure

The work builds on Donald Della Pietra's sufficiently-large-n result and
core proof construction. His missing-even surplus smoothing, totient
profiles, prime-signature ordering, and Hall construction are explicitly
credited. The prior-work comparison distinguishes the completion of the
first question from the separate, already-solved second question.

The [existing forum claim and discussion](https://www.erdosproblems.com/forum/thread/883/proof-claims)
explicitly distinguish Della Pietra's asymptotic theorem from the remaining
small cases. This contribution proves the all-n statement used by the canonical
Lean target. It does not claim to originate the asymptotic resolution or its method.

AI tools were substantially involved in developing, formalizing, and
auditing the proof. This repository makes no claim of historical first
priority, independent human expert peer review, expert endorsement, or
journal acceptance. Human-review declarations in the manuscript remain
for the author to finalize honestly.

## Source integrity

The submitted proof archive SHA256 is
`8f017032cb93f2f0891f6f8200390c161acabf112dac72567462e642b91ede95`.
The Lean source-map SHA256 is
`00d6d094e6d6361ec3d4c60de630635f51023690be910610dc2c0ae2fa90b2c2`.
The release includes the original proof ZIP and the publication package.
