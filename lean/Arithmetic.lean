import Lean

namespace Erdos883Verified

def threshold (n : Nat) : Nat := n / 2 + n / 3 - n / 6
def halfOdds (n : Nat) : Nat := (n + 1) / 2
def retainedOdds (n : Nat) : Nat := n / 3 - n / 6 + 1
def maxHalfLength (n : Nat) : Nat := n / 6

/-- The canonical odd-length range equals the manuscript's half-length range. -/
theorem length_range_iff (n l : Nat) :
    (∃ k, l = 2 * k + 1) ∧ 3 ≤ l ∧ l ≤ n / 3 + 1 ↔
      ∃ k, 1 ≤ k ∧ k ≤ maxHalfLength n ∧ l = 2 * k + 1 := by
  unfold maxHalfLength
  constructor
  · rintro ⟨⟨k, rfl⟩, hlo, hhi⟩
    exact ⟨k, by omega, by omega, rfl⟩
  · rintro ⟨k, hlo, hhi, rfl⟩
    exact ⟨⟨k, rfl⟩, by omega, by omega⟩

theorem threshold_le (n : Nat) : threshold n ≤ n := by
  unfold threshold
  omega

theorem retained_formula (n : Nat) :
    retainedOdds n = threshold n - n / 2 + 1 := by
  unfold retainedOdds threshold
  omega

theorem retained_ge (n : Nat) : maxHalfLength n + 1 ≤ retainedOdds n := by
  unfold maxHalfLength retainedOdds
  omega

theorem halfOdds_le_mono {n u : Nat} (h : n ≤ u) : halfOdds n ≤ halfOdds u := by
  unfold halfOdds
  omega

theorem residue6 (n : Nat) :
    n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega

theorem missing_even_bound_mono {n u : Nat} (h : n ≤ u) :
    halfOdds n - retainedOdds n ≤ halfOdds u - retainedOdds u := by
  unfold halfOdds retainedOdds
  rcases residue6 n with hn | hn | hn | hn | hn | hn <;>
    rcases residue6 u with hu | hu | hu | hu | hu | hu <;> omega

theorem resource_cost_mono {n u : Nat} (h : n ≤ u) :
    n - threshold n + maxHalfLength n ≤ u - threshold u + maxHalfLength u := by
  unfold threshold maxHalfLength
  rcases residue6 n with hn | hn | hn | hn | hn | hn <;>
    rcases residue6 u with hu | hu | hu | hu | hu | hu <;> omega

theorem resource_cost_bound {n u cardA k : Nat}
    (hnu : n ≤ u) (hcard : cardA ≤ n) (hdense : threshold n < cardA)
    (hk : k ≤ maxHalfLength n) :
    (n - cardA) + (k + 1) ≤ u - threshold u + maxHalfLength u := by
  have hmono := resource_cost_mono hnu
  have hthreshold := threshold_le n
  omega

theorem small_n_no_target {n k : Nat} (hn : n < 6) (hk : 1 ≤ k) :
    ¬ k ≤ maxHalfLength n := by
  unfold maxHalfLength
  omega

#print axioms length_range_iff
#print axioms threshold_le
#print axioms retained_formula
#print axioms retained_ge
#print axioms halfOdds_le_mono
#print axioms missing_even_bound_mono
#print axioms resource_cost_mono
#print axioms resource_cost_bound
#print axioms small_n_no_target
end Erdos883Verified
