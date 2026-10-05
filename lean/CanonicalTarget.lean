import Erdos883CycleLengths
import Arithmetic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.GCD.Basic

namespace Erdos883Target

def coprimeGraph : SimpleGraph ℕ := SimpleGraph.fromRel Nat.Coprime

/-- Exactly the proposition on the right side of canonical part (i).
No theorem asserting this proposition is claimed in this checkpoint. -/
def FirstQuestion : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ),
    A ⊆ Finset.Icc 1 n →
    n / 2 + n / 3 - n / 6 < A.card →
    ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
      l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths

def HalfLengthStatement : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ),
    A ⊆ Finset.Icc 1 n →
    n / 2 + n / 3 - n / 6 < A.card →
    ∀ k : ℕ, 1 ≤ k → k ≤ n / 6 →
      2 * k + 1 ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths

/-- The manuscript's indexing does not weaken the canonical cycle-length conclusion. -/
theorem firstQuestion_iff_halfLength : FirstQuestion ↔ HalfLengthStatement := by
  constructor
  · intro h n A hA hd k hk hkn
    have hr := (Erdos883Verified.length_range_iff n (2 * k + 1)).mpr
      ⟨k, hk, hkn, rfl⟩
    exact h n A hA hd _ hr.1 hr.2.1 hr.2.2
  · intro h n A hA hd l hl h3 hln
    obtain ⟨k, hk, hkn, rfl⟩ :=
      (Erdos883Verified.length_range_iff n l).mp ⟨hl, h3, hln⟩
    exact h n A hA hd k hk hkn

/-- All n < 6 cases of the canonical proposition are vacuous. -/
theorem canonical_small_n {n : ℕ} (hn : n < 6) (A : Finset ℕ)
    (l : ℕ) (hl : Odd l) (h3 : 3 ≤ l) (hln : l ≤ n / 3 + 1) :
    l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  obtain ⟨k, hk, hkn, rfl⟩ :=
    (Erdos883Verified.length_range_iff n l).mp ⟨hl, h3, hln⟩
  exact False.elim (Erdos883Verified.small_n_no_target hn hk hkn)

#print axioms firstQuestion_iff_halfLength
#print axioms canonical_small_n
end Erdos883Target
