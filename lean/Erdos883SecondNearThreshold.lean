import Erdos883SecondNearBase

namespace Erdos883Second.Near

/-- A least integer denominator replaces any appeal to real roots. -/
theorem exists_profile_denominator {n t k C : ℕ}
    (ht : 1 ≤ t) (htn : t ≤ n) (hk : 1 ≤ k) (hC : 1 ≤ C) :
    ∃ s : ℕ, 1 ≤ s ∧ 4 * C * n < t * s ^ k ∧
      t * s ^ k ≤ (4 * C * 2 ^ k) * n := by
  have hex : ∃ s : ℕ, 4 * C * n < t * s ^ k := by
    refine ⟨4 * C * n + 1, ?_⟩
    have hp := Nat.le_pow (a := 4 * C * n + 1) (by omega : 0 < k)
    have hm : (4 * C * n + 1) ^ k ≤ t * (4 * C * n + 1) ^ k := by
      simpa using Nat.mul_le_mul_right ((4 * C * n + 1) ^ k) ht
    omega
  let s := Nat.find hex
  have hl : 4 * C * n < t * s ^ k := Nat.find_spec hex
  have hs2 : 2 ≤ s := by
    by_contra hs
    have hsp : s ^ k ≤ 1 := by
      simpa using Nat.pow_le_pow_left (by omega : s ≤ 1) k
    have hmul := Nat.mul_le_mul_left t hsp
    have hbig : n ≤ 4 * C * n := by
      have hc : 1 ≤ 4 * C := by omega
      simpa using Nat.mul_le_mul_right n hc
    omega
  have hprev : t * (s - 1) ^ k ≤ 4 * C * n := by
    have hh := Nat.find_min hex (show s - 1 < s by omega)
    exact Nat.le_of_not_gt hh
  have hsstep : s ≤ 2 * (s - 1) := by omega
  have hp : s ^ k ≤ 2 ^ k * (s - 1) ^ k := by
    simpa only [mul_pow] using Nat.pow_le_pow_left hsstep k
  refine ⟨s, by omega, hl, ?_⟩
  calc
    _ ≤ t * (2 ^ k * (s - 1) ^ k) := Nat.mul_le_mul_left _ hp
    _ = 2 ^ k * (t * (s - 1) ^ k) := by ring
    _ ≤ 2 ^ k * (4 * C * n) := Nat.mul_le_mul_left _ hprev
    _ = _ := by ring

/-- A uniform polynomial estimate used for the fixed rounding budget. -/
theorem scale_budget_of_power {n x D a : ℕ} (hn : 1 ≤ n)
    (hx : x ^ 16 ≤ D * n) (hN : a ^ 16 * D ≤ n) : a * x ≤ n := by
  have hp : (a * x) ^ 16 ≤ n ^ 16 := by
    calc
      _ = a ^ 16 * x ^ 16 := mul_pow _ _ _
      _ ≤ a ^ 16 * (D * n) := Nat.mul_le_mul_left _ hx
      _ = (a ^ 16 * D) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right _ hN
      _ = n ^ 2 := by ring
      _ ≤ n ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
  exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 16 ≠ 0)).mp hp

/-- The small-extra condition turns the profile bound into a linear
candidate budget. -/
theorem small_extra_scale_budget {n t x C D : ℕ}
    (ht : 1 ≤ t) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hl : 4 * C * n < t * x ^ 16) (hu : t * x ^ 16 ≤ D * n)
    (hnear : t * (48 * D) ^ 16 ≤ n) : 48 * t * x ≤ n := by
  have hnn : n ≤ 4 * C * n := by
    have hc : 1 ≤ 4 * C := by omega
    simpa using Nat.mul_le_mul_right n hc
  have hpow : (48 * D) ^ 16 < x ^ 16 :=
    Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt hnear (lt_of_le_of_lt hnn hl))
  have hxd : 48 * D < x :=
    (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 16 ≠ 0)).mp hpow
  have hxp : 48 * D ≤ x ^ 15 := hxd.le.trans (Nat.le_pow (by decide : 0 < 15))
  have hmul : (48 * t * x) * D ≤ n * D := by
    calc
      _ = (t * x) * (48 * D) := by ring
      _ ≤ (t * x) * x ^ 15 := Nat.mul_le_mul_left _ hxp
      _ = t * x ^ 16 := by rw [show 16 = 15 + 1 by decide, pow_succ]; ring
      _ ≤ D * n := hu
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hmul (by omega)

/-- A floor integer error budget satisfies the support power certificate
uniformly once the explicit polynomial threshold is reached. -/
theorem support_certificate_from_scale {n x D K d : ℕ}
    (hn : 1 ≤ n) (hx : 1 ≤ x) (hd : 1 ≤ d)
    (hpow : x ^ 16 ≤ D * n)
    (hN : K ^ (16 * d) * 48 ^ (16 * d) * D ^ d ≤ n) :
    K ^ (16 * d) * n ^ d < (n / (48 * x) + 1) ^ (16 * d) := by
  let r := 16 * d
  let E := n / (48 * x)
  have hr : 0 < r := by dsimp [r]; positivity
  have hxpos : 0 < 48 * x := by positivity
  have hfloor : n < (E + 1) * (48 * x) := by
    simpa only [E, mul_comm] using Nat.lt_mul_div_succ n hxpos
  have hfloorpow : n ^ r < (E + 1) ^ r * (48 * x) ^ r := by
    simpa only [mul_pow] using
      (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (Nat.ne_of_gt hr)).mpr hfloor
  have hxr : x ^ r ≤ D ^ d * n ^ d := by
    dsimp [r]
    simpa only [← pow_mul, mul_pow] using Nat.pow_le_pow_left hpow d
  have hbound : (K ^ r * n ^ d) * (48 * x) ^ r ≤ n ^ r := by
    calc
      _ = K ^ r * 48 ^ r * x ^ r * n ^ d := by rw [mul_pow]; ring
      _ ≤ K ^ r * 48 ^ r * (D ^ d * n ^ d) * n ^ d :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hxr)
      _ = (K ^ r * 48 ^ r * D ^ d) * n ^ (2 * d) := by rw [show 2 * d = d + d by omega, pow_add]; ring
      _ ≤ n * n ^ (2 * d) := Nat.mul_le_mul_right _ hN
      _ = n ^ (2 * d + 1) := by rw [pow_succ]; ring
      _ ≤ n ^ r := Nat.pow_le_pow_right (by omega) (by dsimp [r]; omega)
  exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hbound hfloorpow)

#print axioms exists_profile_denominator
#print axioms scale_budget_of_power
#print axioms small_extra_scale_budget
#print axioms support_certificate_from_scale
end Erdos883Second.Near
