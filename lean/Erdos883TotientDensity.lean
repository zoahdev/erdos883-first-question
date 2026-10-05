import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Algebra.Order.Field.Rat

namespace Erdos883Verified

/-- The rational proportion of residue classes coprime to `n`. -/
def totientDensity (n : ℕ) : ℚ := (Nat.totient n : ℚ) / (n : ℚ)

/-- The totient density is positive on positive integers. -/
theorem totientDensity_pos {n : ℕ} (hn : 0 < n) : 0 < totientDensity n := by
  exact div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hn)) (Nat.cast_pos.mpr hn)

/-- The totient density is always nonnegative, including at zero. -/
theorem totientDensity_nonneg (n : ℕ) : 0 ≤ totientDensity n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The totient density never exceeds one. -/
theorem totientDensity_le_one (n : ℕ) : totientDensity n ≤ 1 := by
  by_cases hn : n = 0
  · simp [totientDensity, hn]
  · apply (div_le_one₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
    exact Nat.cast_le.mpr (Nat.totient_le n)

/-- Euler's formula as an exact finite product for positive integers. -/
theorem totientDensity_eq_prod {n : ℕ} (hn : 0 < n) :
    totientDensity n = ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) := by
  unfold totientDensity
  rw [Nat.totient_eq_mul_prod_factors]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')

/-- The prime support of an lcm is the union of the endpoint supports. -/
theorem primeFactors_lcm {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    (Nat.lcm u v).primeFactors = u.primeFactors ∪ v.primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors_of_ne_zero (Nat.lcm_ne_zero hu.ne' hv.ne'),
    Finset.mem_union, Nat.mem_primeFactors_of_ne_zero hu.ne',
    Nat.mem_primeFactors_of_ne_zero hv.ne']
  constructor
  · rintro ⟨hp, hd⟩
    rcases hp.dvd_lcm.mp hd with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩
  · rintro (⟨hp, hd⟩ | ⟨hp, hd⟩)
    · exact ⟨hp, hp.dvd_lcm.mpr (Or.inl hd)⟩
    · exact ⟨hp, hp.dvd_lcm.mpr (Or.inr hd)⟩

/-- The exact density identity, expressed without division by the gcd density. -/
theorem totientDensity_lcm_mul_gcd {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    totientDensity (Nat.lcm u v) * totientDensity (Nat.gcd u v) =
      totientDensity u * totientDensity v := by
  rw [totientDensity_eq_prod (Nat.lcm_pos hu hv),
    totientDensity_eq_prod (Nat.gcd_pos_of_pos_left v hu),
    totientDensity_eq_prod hu, totientDensity_eq_prod hv,
    primeFactors_lcm hu hv, Nat.primeFactors_gcd hu.ne' hv.ne']
  exact Finset.prod_union_inter

/-- The exact density identity in quotient form. -/
theorem totientDensity_lcm_eq {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    totientDensity (Nat.lcm u v) =
      totientDensity u * totientDensity v / totientDensity (Nat.gcd u v) := by
  apply (eq_div_iff (totientDensity_pos (Nat.gcd_pos_of_pos_left v hu)).ne').mpr
  exact totientDensity_lcm_mul_gcd hu hv

/-- Joining the prime supports costs no more than multiplying the densities. -/
theorem totientDensity_lcm_ge_mul {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    totientDensity u * totientDensity v ≤ totientDensity (Nat.lcm u v) := by
  rw [← totientDensity_lcm_mul_gcd hu hv]
  exact mul_le_of_le_one_right (totientDensity_nonneg _) (totientDensity_le_one _)

/-- Two nonnegative endpoint lower bounds multiply to an lcm-density lower bound. -/
theorem totientDensity_lcm_ge_product {u v : ℕ} {x y : ℚ}
    (hu : 0 < u) (hv : 0 < v) (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxu : x ≤ totientDensity u) (hyv : y ≤ totientDensity v) :
    x * y ≤ totientDensity (Nat.lcm u v) := by
  exact (mul_le_mul hxu hyv hy (totientDensity_nonneg u)).trans
    (totientDensity_lcm_ge_mul hu hv)

/-- In particular, a common nonnegative endpoint lower bound gives its square. -/
theorem totientDensity_lcm_ge_sq {u v : ℕ} {z : ℚ}
    (hu : 0 < u) (hv : 0 < v) (hz : 0 ≤ z)
    (hzu : z ≤ totientDensity u) (hzv : z ≤ totientDensity v) :
    z ^ 2 ≤ totientDensity (Nat.lcm u v) := by
  simpa only [pow_two] using
    totientDensity_lcm_ge_product hu hv hz hz hzu hzv

end Erdos883Verified

#print axioms Erdos883Verified.totientDensity_pos
#print axioms Erdos883Verified.totientDensity_nonneg
#print axioms Erdos883Verified.totientDensity_le_one
#print axioms Erdos883Verified.totientDensity_eq_prod
#print axioms Erdos883Verified.primeFactors_lcm
#print axioms Erdos883Verified.totientDensity_lcm_mul_gcd
#print axioms Erdos883Verified.totientDensity_lcm_eq
#print axioms Erdos883Verified.totientDensity_lcm_ge_mul
#print axioms Erdos883Verified.totientDensity_lcm_ge_product
#print axioms Erdos883Verified.totientDensity_lcm_ge_sq
