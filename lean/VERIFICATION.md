# Erdős 883 automated verification report

## Result

PASS. The final theorem has been checked against the complete canonical all-n statement, with no additional hypotheses.

This is an automated audit using Lean and source/build consistency checks. It is not an independent human review of the proof or its mathematical exposition.

## Exact theorem

The checked constant is `Erdos883Verified.erdos883_firstQuestion`, with type `Erdos883Target.FirstQuestion`. The audit also checks it against the following unabbreviated canonical statement:

```lean
∀ (n : ℕ) (A : Finset ℕ),
  A ⊆ Finset.Icc 1 n →
  n / 2 + n / 3 - n / 6 < A.card →
  ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
    l ∈ ((SimpleGraph.fromRel Nat.Coprime).induce (A : Set ℕ)).oddCycleLengths
```

There is no lower bound on `n` and no additional certificate or analytic hypothesis. The density expression uses natural-number division. The graph is the induced coprime graph on `A`, and the cycle notion is the canonical `Walk.IsCycle` definition.

The reference is the right-hand side of part (i) in `FormalConjectures/ErdosProblems/883.lean` at formal-conjectures commit `89294ea02bd7cd678d59984add52cb4baef3dbf4`. The named target is token-identical to that right-hand side, and the local cycle definitions match the canonical source byte-for-byte. This verifies the positive mathematical assertion; it does not modify the upstream file or address part (ii).

## Kernel assumptions and safety checks

The final constant's reported axioms are exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

The final local source closure was checked for unproved placeholders, custom axioms, native/unsafe reflection, kernel-checking bypass options, and compiler trust escapes. No such constructs were found.

These checks rely on Lean's kernel and the pinned dependencies. They are not a separate implementation of the kernel or a bootstrap of Lean and mathlib from source.

## Frozen source and build evidence

- Audit completed in UTC: 2026-10-05T07:50:03.657934+00:00
- Lean toolchain: `leanprover/lean4:v4.33.1`
- Mathlib commit: `0df444a360eaa60ab8c11dca51a86af692955474`
- Final local import closure: 6,831 modules, 144,287,247 source bytes
- Source-map SHA-256: `00d6d094e6d6361ec3d4c60de630635f51023690be910610dc2c0ae2fa90b2c2`
- Final root source SHA-256: `14ad12ae94ac982fe25f508c28eaa1c2bcc8d7c22e0fcc399012165b4c021f98`
- Checked root object SHA-256: `9af042ff1142aead23cdaf22d1d995bacb8c8a04b2aed691b278ca76b57d7f70`

`PROVENANCE.json` and `MODULES.txt` identify the exact source closure and pinned dependencies. `FINAL_AUDIT.json` records the automated audit results and source hashes. `FINAL_COMPILE_RECORD.json` and `FINAL_AXIOMS.log` retain the final root compilation evidence. `VERIFY_CANONICAL.lean` and `CANONICAL_AUDIT.log` retain the explicit canonical-type and axiom checks.

The verification combines modular kernel source compilation during construction, targeted recompilation of concrete correspondence concerns, and a fresh frozen-input compilation of the final root. All source, object, and configuration hashes in the frozen audit snapshot remained unchanged during the final check.

This is not a second clean rebuild of every certificate. Some earlier successful module compilations were witnessed during execution without durable per-module pre/post hash records. Those are historical operational evidence. Empty logs, completion markers, and timestamps alone are not treated as frozen-input attestations. The audit found and resolved the concrete stale-source concerns through targeted builds and object/declaration comparisons.

The archive contains the final root's exact local import closure, with verification documentation and its checking harness. Historical checkpoints and unrelated experimental modules are outside this proof-source closure.

## Reproducing the checks

Use the pinned toolchain and dependencies. From the archive root, run:

```sh
bash verify.sh
LEAN_PATH=.:${LEAN_PATH:-} lake env lean -M4096 VERIFY_CANONICAL.lean
```

`verify.sh` compiles the listed modules in dependency order with Lean's 4096 MiB per-process limit. A full clean replay may take substantial time. The expected final axiom list contains only the three assumptions above. Source hashes can be checked against the included manifests; compiled object bytes need not be identical across separate successful builds.
