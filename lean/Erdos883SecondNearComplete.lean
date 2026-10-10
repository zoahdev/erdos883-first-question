import Erdos883SecondNearParameters
import Erdos883SecondNearThreshold

namespace Erdos883Second.Near
set_option maxHeartbeats 2000000

/-- The order is intentionally ample: an integer-only construction makes all
uniform errors sublinear without invoking real exponentiation. -/
def nearMomentOrder (l : ℕ) : ℕ := 16 * (l + 1)
def nearMomentInteger (l : ℕ) : ℕ := 2 ^ momentExponent (nearMomentOrder l)
def nearDenominatorConstant (l : ℕ) : ℕ :=
  4 * nearMomentInteger l * 2 ^ nearMomentOrder l
def nearMultiplier (l : ℕ) : ℕ := (48 * nearDenominatorConstant l) ^ 16
def nearThreshold (l : ℕ) : ℕ :=
  max 1 (max
    ((48 * (l + 1)) ^ 16 * nearDenominatorConstant l)
    (supportConstant (nearMomentOrder l) ^ nearMomentOrder l *
      48 ^ nearMomentOrder l * nearDenominatorConstant l ^ (l + 1)))

/-- A complete uniform near-U theorem, with explicit natural thresholds.
The constants are very large; the theorem makes no numerical efficiency claim. -/
theorem near_tripartite {n l : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 n)
    (hcard : n / 2 + n / 3 - n / 6 < A.card)
    (hN : nearThreshold l ≤ n)
    (hnear : (A \ standardUniverse n).card * nearMultiplier l ≤ n) :
    ContainsTripartite A l := by
  let d := l + 1
  let k := nearMomentOrder l
  let C := nearMomentInteger l
  let D := nearDenominatorConstant l
  let K := supportConstant k
  let t := (A \ standardUniverse n).card
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hk : 1 ≤ k := by dsimp [k, nearMomentOrder]; omega
  have hC : 1 ≤ C := Nat.one_le_pow _ _ (by decide : 0 < 2)
  have hD : 1 ≤ D := by
    change 1 ≤ 4 * C * 2 ^ k
    have hp : 0 < 4 * C * 2 ^ k := Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (Nat.pow_pos (by decide))
    omega
  have hn : 1 ≤ n := (le_max_left _ _).trans hN
  have ht : 1 ≤ t := by
    have hh := missing_lt_extra hcard
    dsimp [t]
    omega
  have hM : 1 ≤ nearMultiplier l := by
    change 1 ≤ (48 * D) ^ 16
    exact Nat.one_le_pow _ _ (Nat.mul_pos (by decide) (by omega))
  have htn : t ≤ n := by
    calc
      _ = t * 1 := by simp
      _ ≤ t * nearMultiplier l := Nat.mul_le_mul_left _ hM
      _ ≤ n := hnear
  obtain ⟨s, hs, hprofile, hupper⟩ := exists_profile_denominator ht htn hk hC
  let x := s ^ d
  let E := n / (48 * x)
  have hx : 1 ≤ x := Nat.one_le_pow _ _ (by omega)
  have hxk : x ^ 16 = s ^ k := by
    dsimp [x, k, nearMomentOrder, d]
    rw [← pow_mul]
    congr 1
    omega
  have hlow : 4 * C * n < t * x ^ 16 := by simpa only [hxk] using hprofile
  have hupper' : t * x ^ 16 ≤ D * n := by
    simpa only [hxk, D, nearDenominatorConstant, C, k] using hupper
  have hpow : x ^ 16 ≤ D * n := by
    have hh : x ^ 16 ≤ t * x ^ 16 := by
      simpa using Nat.mul_le_mul_right (x ^ 16) ht
    exact hh.trans hupper'
  have hsmall : 48 * t * x ≤ n :=
    small_extra_scale_budget ht hC hD hlow hupper' hnear
  have hNb : (48 * d) ^ 16 * D ≤ n := by
    exact (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hl : 48 * d * x ≤ n := scale_budget_of_power hn hpow hNb
  have hE : 48 * E * x ≤ n := by
    simpa only [E, mul_assoc, mul_left_comm, mul_comm] using Nat.div_mul_le_self n (48 * x)
  have hNs : K ^ (16 * d) * 48 ^ (16 * d) * D ^ d ≤ n := by
    exact (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have herr : supportConstant k ^ k * n ^ (l + 1) < (E + 1) ^ k := by
    exact support_certificate_from_scale hn hx hd hpow hNs
  have hCQ : momentConstant k = (C : ℚ) := by
    simp only [momentConstant, C, nearMomentInteger, k, Nat.cast_pow, Nat.cast_ofNat]
  exact finite_tripartite_of_integer_budgets hA hcard hs hCQ hprofile hsmall hl hE herr

/-- A positive density neighborhood and one threshold work for every selected
set. This is the near branch needed by the eventual second-question theorem. -/
theorem near_tripartite_eventually (l : ℕ) :
    ∃ δ : ℚ, 0 < δ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → n / 2 + n / 3 - n / 6 < A.card →
      ((A \ standardUniverse n).card : ℚ) ≤ δ * n → ContainsTripartite A l := by
  have hM : 0 < nearMultiplier l := by
    change 0 < (48 * (4 * (2 ^ momentExponent (nearMomentOrder l)) * 2 ^ nearMomentOrder l)) ^ 16
    exact Nat.pow_pos (Nat.mul_pos (by decide) (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide))))
  refine ⟨(nearMultiplier l : ℚ)⁻¹, by positivity, nearThreshold l, ?_⟩
  intro n hn A hA hcard hnear
  apply near_tripartite hA hcard hn
  have hMQ : (0 : ℚ) < nearMultiplier l := by exact_mod_cast hM
  have hh : ((A \ standardUniverse n).card : ℚ) * nearMultiplier l ≤ n := by
    have hmul := mul_le_mul_of_nonneg_right hnear hMQ.le
    simpa only [mul_assoc, mul_left_comm, inv_mul_cancel₀ (ne_of_gt hMQ), mul_one] using hmul
  exact_mod_cast hh

#print axioms near_tripartite
#print axioms near_tripartite_eventually
end Erdos883Second.Near


