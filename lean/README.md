# Erdős 883: the first question

The main declaration is `Erdos883Verified.erdos883_firstQuestion` in
`Erdos883VerifiedCoverage.lean`. Its type is exactly
`Erdos883Target.FirstQuestion`, defined in `CanonicalTarget.lean`.

For every natural number n and every subset A of {1,…,n} with

    |A| > floor(n/2) + floor(n/3) − floor(n/6),

the graph joining distinct elements of A when they are coprime contains a
cycle of every odd length 2ℓ+1 with 1 ≤ ℓ ≤ floor(n/6).
The canonical formulation quantifies odd lengths l satisfying
3 ≤ l ≤ floor(n/3)+1; the equivalence is proved in the source.

This package concerns the first question only. It makes no claim about the
separate second question on the Erdős problem page.

## Verification and trusted dependencies

The Lean and mathlib revisions, complete local source dependency closure,
source hashes, and canonical statement revision are recorded in
`PROVENANCE.json`. `FINAL_AXIOMS.log` reports the dependencies of the actual
main theorem: `propext`, `Classical.choice`, and `Quot.sound`.

The delivered proof uses ordinary Lean kernel checking. It introduces no
custom axioms, admitted proofs, or native-evaluation proof shortcuts.
Numerical certificates are exact arithmetic statements checked by Lean.
External generators produce candidate data; their output is accepted only
through the checked mathematical certificate criteria.

The verification record consists of modular kernel compilation of the
sources and fresh compilation of the final theorem, together with an
separate automated statement, dependency, and provenance audit. This is not a claim
of independent human review, or that the entire final project was rebuilt a second time in a
clean environment. See the accompanying audit report for the evidence and
any qualifications.

## Reproduce

Install the official Lean toolchain selected by `lean-toolchain`. Fetch the
locked mathlib dependencies through Lake and obtain their corresponding
compiled cache. With Python 3 available, run `bash verify.sh` from this directory. The script
compiles every local module in dependency order, sequentially, with Lean's
4096 MiB allocation cap then checks the explicit raw canonical statement and prints the final axiom report. Actual process
resident memory can exceed Lean's internal allocation cap.

No generated local `.olean` files are required in the source package. The
source build may require substantial time because its finite arithmetic
certificates are kernel checked. `MODULES.txt` lists the exact build order.

## Proof structure

The graph-theoretic argument constructs the required odd cycles from
retained odd vertices, coprime endpoints, an ordered prime-signature
skeleton, and distinct even neighbor representatives. An elementary
endpoint lemma is proved directly in Lean; the formal proof does not assume
an external Ahlswede–Khachatrian theorem.

Finite arithmetic certificates cover all n below 200000. A formal analytic
argument proves the remaining range n ≥ 200000. The final declaration joins
these ranges into the canonical universally quantified statement.

Source provenance and the original candidate manuscript revision are
recorded for traceability; the Lean declarations and their kernel checks
are the basis of the formal result.

The copied `Erdos883CycleLengths.lean` retains the Formal Conjectures Authors’
Apache-2.0 notice. Its license text is included as `FORMAL_CONJECTURES_LICENSE`.
