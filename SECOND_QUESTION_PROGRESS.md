# Independent second-question development for Erdős 883

This branch contains a complete **mathematical proof proposed for review** of the second question, together with a partially completed Lean development. It does not contain a Lean theorem proving the full second question. No prize acceptance, external expert endorsement, award amount, sole historical priority or complete formalization is asserted.

The independent mathematical argument is in `paper/second-question/independent-proof-20261010.md`. It handles the exact threshold and both the near-extremal and positive-distance regimes, using finite totient moments, CRT signatures, uniformly bounded L2 couplings, finite spectral stability and elementary bipartite star counting. It was developed without reading or copying an existing second-question proof or its Lean code. Gábor N. Sárközy's 1999 resolution remains the historical mathematical result; this argument does not claim its first discovery.

The existing first-question proof and manuscript, frozen under their original source provenance, remain in this repository. Donald Della Pietra's earlier asymptotic architecture and all actual dependencies retain their attribution. General first-question helper lemmas are explicitly imported by some new Lean modules.

## Verified Lean scope

The new modules under `lean/` establish the following:

- `Erdos883SecondQuestion.lean`: the positive-parameter second-question target and a non-induced `K(1,l,l)` represented by an injective graph homomorphism; an arithmetic witness equivalence.
- `Erdos883SecondQuestionFinsets.lean`: an equivalent finite-set witness with an apex, two disjoint size-l parts and all required cross-part coprimality conditions.
- `Erdos883SecondQuestionOne.lean`, `Erdos883SecondQuestionOneVerified.lean`: only the l=1 subcase, with N=6, derived from the existing first-question theorem.
- `Erdos883SecondPrimeSupport.lean`: a uniform prime-support error estimate using integer powers and an explicit constant.
- `Erdos883SecondMoment.lean`, `Erdos883SecondMomentBound.lean`: arbitrary positive-order inverse-totient moments and a fully finite explicit Euler-product bound.
- `Erdos883SecondCounts.lean`: arithmetic candidate counts and the required coprimality implications. The verified left count has the slightly coarser error `2*2^omega(a)+1`; a future Lean assembly must use that bound rather than silently using the sharper manuscript estimate.
- `Erdos883SecondGoodProfiles.lean`: finite Markov counting of low-totient values and selection of a good value from a subset exceeding the proven moment budget.

All recorded completed checks use Lean 4.33.1 and mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The audited new theorem entries printed only `propext`, `Classical.choice` and `Quot.sound`. Existing first-question compiled objects and pinned dependency objects were reused. This is not a new clean rebuild of all 6,831 first-question modules. Source integrity against its existing provenance was checked separately.

## Reproduction

First prepare the existing first-question dependency closure using `lean/verify.sh` and the corrections in `REPRODUCTION_ERRATA.txt`: Python >=3.9 and a larger memory cap for `Erdos883SmallCertificate117` are required. The untouched script's fixed 4096 MiB cap is not claimed to pass that module. After the first-question objects exist in `lean/`, run `bash lean/verify-second-question-progress.sh` to check these new modules in dependency order. Logs distinguish the l=1 result from the full unproved Lean target.

## Authorship and submission status

The applicant is Yicheng Pan (潘奕成), GitHub `zoahdev`. His reported role is proposing the goal, organizing and directing AI-assisted work, and reviewing existing material. Mathematical reasoning, Lean programming, checking and writing involved substantial OpenAI Codex assistance. Exact historical first-question model identifiers are not established here. The applicant's review statement is not external expert review and does not automatically cover later material.

The official eligibility inquiry is https://github.com/TheJustinSunPrize/awards/issues/4969. Complete mathematical evidence may be submitted for mathematical review before full Lean verification; public award review and payment still require the official conditions. Only the actual completed mathematical and formalization contributions are claimed.
