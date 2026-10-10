# Erdős 883: complete second question and two-question audit

The second-question theorem is `Erdos883Second.secondQuestion` in
`Erdos883SecondFarComplete.lean`. The combined theorem is
`Erdos883Verified.erdos883_bothQuestions` in
`Erdos883SecondCompleteAudit.lean`.

For every fixed positive integer l, there is N such that every n ≥ N and
every A ⊆ {1,...,n} with

    floor(n/2) + floor(n/3) - floor(n/6) < |A|

have a complete tripartite K(1,l,l) subgraph in the coprime graph. All 2l+1
vertices are distinct. Additional edges within the two large parts are allowed.
The threshold is uniform over A. The combined theorem also proves the original
first question for every natural n and every required odd simple cycle length.

The explicit arithmetic witness theorem
`Erdos883Verified.erdos883_secondQuestion_raw` checks membership, injectivity,
disjointness and every required cross-part coprimality without using a graph
containment abbreviation as its conclusion. The first-question raw statement is
checked against `SimpleGraph.fromRel Nat.Coprime`; cycle lengths require IsCycle.

## Proof and attribution

The new second-question development independently derives the near-U branch,
finite signature model, CRT errors, graph-link estimates, large-prime tail,
finite couplings, Fourier stability, six-position averaging and final uniform
quantifiers. `Erdos883SecondAssembly.lean` has an explicit far-branch premise;
`Erdos883SecondFarComplete.lean` proves and discharges that premise. No such
premise remains in `secondQuestion` or the combined target.

The second question was historically solved by Gábor N. Sárközy in 1999. This
is a new proof of an already-known result, not a claim of its first discovery.
The first-question theorem retains Donald Della Pietra's credited asymptotic
work and architecture and Yicheng Pan's stated finite-completion contribution.
The earlier second-question formalization by baobingzhang is acknowledged as
prior work; it was not copied or transplanted into this new derivation.

Yicheng Pan (潘奕成), GitHub zoahdev, reports proposing the goal and organizing
and directing the AI-assisted work. AI agents substantially performed reasoning,
formalization, checking and writing. No independent external human expert
endorsement, historical global priority, official prize acceptance or fixed
award amount is asserted. The official submission remains subject to review.

## Self-check scope

Lean 4.33.1 and mathlib 0df444a360eaa60ab8c11dca51a86af692955474 are pinned.
The complete second-question and combined-audit source dependency closure
contains 57 local modules. The complete source manifest, per-module receipts,
logs, final axiom output and separate AI-assisted statement review are in
`../audit/complete-second-question-20261010/`.

All 57 local modules were recompiled in dependency order. The actual first,
second and combined target theorems report only:

    [propext, Classical.choice, Quot.sound]

The new run reused pinned standard dependency objects and the earlier
independently rebuilt first-question objects. It was not a new complete rebuild
of first-question sources or mathlib. The earlier first-question independent
6,831-module rebuild remains documented separately in `../audit/`.

## Reproduce from the selected source commit

Use the full commit SHA selected in the official submission. Clone the original
repository, check out that exact SHA, and enter `lean/`. Install the Lean version
specified by `lean-toolchain`; Python ≥ 3.9, Bash, Lake, sufficient disk and
memory are required.

    lake exe cache get
    bash verify-second-question.sh

The portable verifier validates the frozen first-question source hashes,
compiles its complete local MODULES.txt closure and raw canonical audit, then
compiles the dynamically derived second-question source closure and the final
combined audit. It uses the pinned standard dependency caches; it does not
rebuild all of mathlib. The Chinese Remainder dependency is built by Lake if its
matching object is absent from the fetched cache.

The memory cap defaults to 8192 MiB, because first-question certificate 117
needs the documented higher cap. `LEAN_MEMORY_MIB` can set an appropriate cap.
The original historical `verify.sh` is preserved and its 4096-MiB issue remains
documented in `../REPRODUCTION_ERRATA.txt`. Full first-question reproduction is
substantial work; this guide does not suggest that the old script passes
unchanged or that full source reproduction is instantaneous.

For a subsequent second-question-only recheck after the complete first-question
objects have been built, run `bash verify-second-question.sh --reuse-first-objects`.
That mode verifies the direct first-question object inputs and records their
reuse; it does not claim to recompile first-question sources in that run.
The target axiom audit must still be read; compilation alone does not establish
organizer acceptance, historical priority or human authorship.
