import Erdos883SecondMomentBound
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-! A finite three-coordinate disjoint-signature coupling and its uniform
product L2 bound. This is a supporting lemma, not the full arithmetic coupling
construction or the second-question theorem. -/

namespace Erdos883Second.Far

noncomputable section

def bernoulliMass (q : ℚ) (b : Bool) : ℚ := if b then q else 1 - q

def tripleProductMass (q : ℚ) (x : Bool × Bool × Bool) : ℚ :=
  bernoulliMass q x.1 * bernoulliMass q x.2.1 * bernoulliMass q x.2.2

def disjointTripleMass (q : ℚ) : Bool × Bool × Bool → ℚ
  | (false, false, false) => 1 - 3 * q
  | (true, false, false) => q
  | (false, true, false) => q
  | (false, false, true) => q
  | _ => 0

def tripleL2Square (q : ℚ) : ℚ :=
  ∑ x : Bool × Bool × Bool, (disjointTripleMass q x)^2 / tripleProductMass q x

theorem disjointTripleMass_sum (q : ℚ) :
    (∑ x : Bool × Bool × Bool, disjointTripleMass q x) = 1 := by
  simp [Fintype.sum_prod_type, disjointTripleMass]
  ring

theorem tripleL2Square_identity {q : ℚ} (hq : q ≠ 0) (hq1 : q ≠ 1) :
    tripleL2Square q = 1 + (3 * q^2 + q^3) / (1 - q)^3 := by
  have hd : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  simp [tripleL2Square, Fintype.sum_prod_type,
    disjointTripleMass, tripleProductMass, bernoulliMass]
  field_simp [hq, hd]
  ring

theorem tripleL2Square_nonneg {q : ℚ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ tripleL2Square q := by
  have hw : ∀ b, 0 ≤ bernoulliMass q b := by
    intro b
    cases b <;> simp [bernoulliMass] <;> linarith
  apply Finset.sum_nonneg
  intro x _
  exact div_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _))

theorem tripleL2Square_upper {q : ℚ} (hq : 0 < q) (hq_small : q ≤ 1 / 5) :
    tripleL2Square q ≤ 1 + 7 * q^2 := by
  have hq1 : q ≠ 1 := by linarith
  rw [tripleL2Square_identity (ne_of_gt hq) hq1]
  have hd : 0 < (1 - q)^3 := pow_pos (by linarith) _
  have hpow : (4 / 5 : ℚ)^3 ≤ (1 - q)^3 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hbase : 3 + q ≤ 7 * (1 - q)^3 := by norm_num at hpow; linarith
  have hscaled := mul_le_mul_of_nonneg_left hbase (sq_nonneg q)
  have hquot : (3 * q^2 + q^3) / (1 - q)^3 ≤ 7 * q^2 :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  linarith

theorem tripleL2Square_prime_factor {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    tripleL2Square (1 / p) ≤
      ((p : ℚ)^2 / ((p : ℚ)^2 - 1))^7 := by
  have hpq : (5 : ℚ) ≤ p := by exact_mod_cast hp5
  have hp0 : (0 : ℚ) < p := by linarith
  have hp2 : (0 : ℚ) < (p : ℚ)^2 := sq_pos_of_pos hp0
  have hd : (0 : ℚ) < (p : ℚ)^2 - 1 := by nlinarith
  have hq_small : (1 : ℚ) / p ≤ 1 / 5 :=
    one_div_le_one_div_of_le (by norm_num) hpq
  have hupper := tripleL2Square_upper (one_div_pos.mpr hp0) hq_small
  have hb := one_add_mul_sub_le_pow
    (show (-1 : ℚ) ≤ 1 + 1 / (p : ℚ)^2 by
      have hh : (0 : ℚ) ≤ 1 / (p : ℚ)^2 := div_nonneg (by norm_num) (sq_nonneg _)
      linarith) 7
  have hb' : 1 + 7 / (p : ℚ)^2 ≤ (1 + 1 / (p : ℚ)^2)^7 := by
    norm_num only at hb
    simpa only [add_sub_cancel_left, mul_one_div] using hb
  have hk : 1 + 1 / (p : ℚ)^2 ≤ (p : ℚ)^2 / ((p : ℚ)^2 - 1) := by
    have hfrac := one_div_le_one_div_of_le hd
      (show (p : ℚ)^2 - 1 ≤ (p : ℚ)^2 by linarith)
    have he : 1 + 1 / ((p : ℚ)^2 - 1) = (p : ℚ)^2 / ((p : ℚ)^2 - 1) := by
      field_simp
      ring
    linarith
  calc
    _ ≤ 1 + 7 / (p : ℚ)^2 := by simpa only [div_pow, one_pow, mul_one_div] using hupper
    _ ≤ _ := hb'
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hk _

theorem tripleL2Square_product_bound (n : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p) (hn : ∀ p ∈ P, p ≤ n) :
    (∏ p ∈ P, tripleL2Square (1 / p)) ≤ (2 : ℚ)^7 := by
  have hprod : (∏ p ∈ P, tripleL2Square (1 / p)) ≤
      ∏ p ∈ P, ((p : ℚ)^2 / ((p : ℚ)^2 - 1))^7 := by
    apply Finset.prod_le_prod
    · intro p hp
      apply tripleL2Square_nonneg (by positivity)
      have hpq : (1 : ℚ) ≤ p := by exact_mod_cast (hP p hp).1.one_le
      exact (div_le_iff₀ (by positivity : (0 : ℚ) < p)).mpr (by simpa using hpq)
    · intro p hp; exact tripleL2Square_prime_factor (hP p hp).1 (hP p hp).2
  calc
    _ ≤ _ := hprod
    _ = (∏ p ∈ P, (p : ℚ)^2 / ((p : ℚ)^2 - 1))^7 := Finset.prod_pow _ _ _
    _ ≤ (2 : ℚ)^7 := pow_le_pow_left₀
      (Finset.prod_nonneg fun p hp => by
        have hpq : (5 : ℚ) ≤ p := by exact_mod_cast (hP p hp).2
        apply div_nonneg (sq_nonneg _)
        nlinarith)
      (Erdos883Second.Near.prime_telescope_prod_le_two n P (fun p hp => (hP p hp).1) hn) _

end

end Erdos883Second.Far

#print axioms Erdos883Second.Far.disjointTripleMass_sum
#print axioms Erdos883Second.Far.tripleL2Square_identity
#print axioms Erdos883Second.Far.tripleL2Square_upper
#print axioms Erdos883Second.Far.tripleL2Square_product_bound
