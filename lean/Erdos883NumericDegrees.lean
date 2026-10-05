import Erdos883NumericDegreesCore
import Erdos883AdaptiveDegrees
import Mathlib.Algebra.Order.Floor.Semifield

namespace Erdos883Verified

def numericDegree (scale W p U a b : ℕ) : ℕ :=
  coreNumericDegree scale W ((p - 1) ^ Nat.log p U) (p ^ Nat.log p U) a b

theorem rational_max_common_denominator (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    max (((a : ℚ) / b) ^ 2) (((a : ℚ) / b) * ((c : ℚ) / d)) =
      (max (a ^ 2 * d) (a * b * c) : ℕ) / ((b ^ 2 * d : ℕ) : ℚ) := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h1 : ((a : ℚ) / b)^2 = (a^2*d : ℚ)/(b^2*d) := by field_simp
  have h2 : ((a : ℚ) / b)*((c : ℚ)/d) = (a*b*c : ℚ)/(b^2*d) := by field_simp
  rw [h1, h2, max_div_div_right (by positivity)]
  push_cast
  rfl

theorem coreNumericDegree_eq_floor (scale W c d a b : ℕ) (hb : 0 < b) (hd : 0 < d) :
    coreNumericDegree scale W c d a b =
      ⌊(scale : ℚ) * max (((a : ℚ)/b)^2) (((a : ℚ)/b)*((c : ℚ)/d)) -
        coprimeDiscrepancyError W⌋₊ := by
  rw [rational_max_common_denominator a b c d hb hd, Nat.floor_sub_natCast]
  rw [← mul_div_assoc, ← Nat.cast_mul, Nat.floor_div_eq_div]
  rfl

theorem numericDegree_eq_adaptiveDegree (scale W p U a b : ℕ)
    (hp : 2 ≤ p) (hb : 0 < b) :
    numericDegree scale W p U a b = adaptiveDegree scale U W p ((a : ℚ)/b) := by
  unfold numericDegree adaptiveDegree adaptiveDensityLower adaptiveTailFactor
  rw [coreNumericDegree_eq_floor _ _ _ _ _ _ hb (pow_pos (by omega) _)]
  congr 3
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  simp only [div_pow]

#print axioms rational_max_common_denominator
#print axioms coreNumericDegree_eq_floor
#print axioms numericDegree_eq_adaptiveDegree
end Erdos883Verified
