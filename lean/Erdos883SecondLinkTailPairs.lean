import Erdos883SecondLinkTriangles
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Actual prefix pairs sharing a divisor above a fixed cutoff.
The union includes every integer divisor above the cutoff, so a fortiori
contains every pair sharing a large prime. -/

namespace Erdos883Second.Link

open scoped BigOperators

noncomputable def multiplesPrefix (n p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun x => p ∣ x)

theorem multiplesPrefix_eq_image (n p : ℕ) (hp : 0 < p) :
    multiplesPrefix n p = (Finset.Icc 1 (n / p)).image (fun a => p * a) := by
  classical
  ext x
  simp only [multiplesPrefix, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hx1, hxn⟩, a, rfl⟩
    refine ⟨a, ⟨?_, ?_⟩, rfl⟩
    · by_contra h
      have ha : a = 0 := by omega
      simp [ha] at hx1
    · exact (Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using hxn)
  · rintro ⟨a, ⟨ha1, han⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, dvd_mul_right p a⟩
    · have := Nat.mul_pos hp (show 0 < a by omega)
      omega
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp han

theorem multiplesPrefix_card (n p : ℕ) (hp : 0 < p) :
    (multiplesPrefix n p).card = n / p := by
  classical
  rw [multiplesPrefix_eq_image n p hp,
    Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp h)]
  simp

noncomputable def sharedDivisorPairs (n P : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc (P + 1) n).biUnion fun p =>
    (multiplesPrefix n p).product (multiplesPrefix n p)

theorem mem_sharedDivisorPairs {n P x y p : ℕ}
    (hx : x ∈ Finset.Icc 1 n) (hy : y ∈ Finset.Icc 1 n)
    (hP : P < p) (hpn : p ≤ n) (hpx : p ∣ x) (hpy : p ∣ y) :
    (x, y) ∈ sharedDivisorPairs n P := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨p, Finset.mem_Icc.mpr ⟨by omega, hpn⟩, ?_⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hx, hpx⟩,
    Finset.mem_filter.mpr ⟨hy, hpy⟩⟩

theorem sharedDivisorPairs_card_le_sum (n P : ℕ) :
    (sharedDivisorPairs n P).card ≤
      ∑ p ∈ Finset.Icc (P + 1) n, (n / p)^2 := by
  classical
  calc
    _ ≤ ∑ p ∈ Finset.Icc (P + 1) n,
        ((multiplesPrefix n p).product (multiplesPrefix n p)).card :=
      Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : 0 < p := by have := (Finset.mem_Icc.mp hp).1; omega
      simpa only [Finset.product_eq_sprod, multiplesPrefix_card n p hp0, pow_two] using
        Finset.card_product (multiplesPrefix n p) (multiplesPrefix n p)

theorem reciprocal_square_step {p : ℕ} (hp : 2 ≤ p) :
    1 / (p : ℝ)^2 ≤ 1 / (p - 1 : ℕ) - 1 / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hmR : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 0 < p - 1 by omega)
  have hcast : ((p - 1 : ℕ) : ℝ) = p - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  rw [hcast]
  have hm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  field_simp
  nlinarith

theorem reciprocal_square_tail_sum_le (n P : ℕ) (hP : 1 ≤ P) :
    (∑ p ∈ Finset.Icc (P + 1) n, 1 / (p : ℝ)^2) ≤ 1 / (P : ℝ) := by
  by_cases hPn : P ≤ n
  · have hsum : (∑ p ∈ Finset.Icc (P + 1) n, 1 / (p : ℝ)^2) ≤
        1 / (P : ℝ) - 1 / (n : ℝ) := by
      induction n, hPn using Nat.le_induction with
      | base => simp
      | succ n hPn ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hstep := reciprocal_square_step (show 2 ≤ n + 1 by omega)
        have hpred : n + 1 - 1 = n := by omega
        rw [hpred] at hstep
        linarith
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith
  · have hemp : Finset.Icc (P + 1) n = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hemp]
    simp only [Finset.sum_empty]
    positivity

theorem sharedDivisorPairs_card_real_le (n P : ℕ) (hP : 1 ≤ P) :
    ((sharedDivisorPairs n P).card : ℝ) ≤ (n : ℝ)^2 / P := by
  classical
  have hsum : ((sharedDivisorPairs n P).card : ℝ) ≤
      ∑ p ∈ Finset.Icc (P + 1) n, (((n / p : ℕ) : ℝ)^2) := by
    exact_mod_cast sharedDivisorPairs_card_le_sum n P
  calc
    _ ≤ _ := hsum
    _ ≤ (n : ℝ)^2 * ∑ p ∈ Finset.Icc (P + 1) n, 1 / (p : ℝ)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : 0 < p := by have := (Finset.mem_Icc.mp hp).1; omega
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
      have hmul : ((n / p : ℕ) : ℝ) * p ≤ n := by
        exact_mod_cast Nat.div_mul_le_self n p
      have hfloor : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / p :=
        (le_div_iff₀ hpR).mpr hmul
      have hsquare := pow_le_pow_left₀ (by positivity) hfloor 2
      simpa only [div_pow, mul_one_div] using hsquare
    _ ≤ (n : ℝ)^2 * (1 / P) :=
      mul_le_mul_of_nonneg_left (reciprocal_square_tail_sum_le n P hP) (sq_nonneg _)
    _ = _ := by rw [mul_one_div]

/-- Pairwise disjoint prime signatures through the finite cutoff. -/
def smallPrimeDisjoint (P x y : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ P → ¬ (p ∣ x ∧ p ∣ y)

theorem noncoprime_mem_sharedDivisorPairs {n P x y : ℕ}
    (hx : x ∈ Finset.Icc 1 n) (hy : y ∈ Finset.Icc 1 n)
    (hsmall : smallPrimeDisjoint P x y) (hcop : ¬ Nat.Coprime x y) :
    (x, y) ∈ sharedDivisorPairs n P := by
  obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hPp : P < p := by
    by_contra h
    exact hsmall p hp (by omega) ⟨hpx, hpy⟩
  have hp_le : p ≤ n :=
    (Nat.le_of_dvd (show 0 < x by have := (Finset.mem_Icc.mp hx).1; omega) hpx).trans
      (Finset.mem_Icc.mp hx).2
  exact mem_sharedDivisorPairs hx hy hPp hp_le hpx hpy

noncomputable def largePrimeNoncoprimePairs (n P : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 n).product (Finset.Icc 1 n)).filter
    (fun xy => smallPrimeDisjoint P xy.1 xy.2 ∧ ¬ Nat.Coprime xy.1 xy.2)

/-- The real prefix error `n²/P` applies to actual noncoprime pairs whose
small-prime signatures are disjoint, without any model assumption. -/
theorem largePrimeNoncoprimePairs_card_real_le (n P : ℕ) (hP : 1 ≤ P) :
    ((largePrimeNoncoprimePairs n P).card : ℝ) ≤ (n : ℝ)^2 / P := by
  classical
  have hsubset : largePrimeNoncoprimePairs n P ⊆ sharedDivisorPairs n P := by
    intro xy hxy
    obtain ⟨hmem, hsmall, hcop⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hmem
    exact noncoprime_mem_sharedDivisorPairs hx hy hsmall hcop
  have hcard : ((largePrimeNoncoprimePairs n P).card : ℝ) ≤
      (sharedDivisorPairs n P).card := by exact_mod_cast Finset.card_le_card hsubset
  exact hcard.trans (sharedDivisorPairs_card_real_le n P hP)

#print axioms multiplesPrefix_card
#print axioms sharedDivisorPairs_card_le_sum
#print axioms reciprocal_square_tail_sum_le
#print axioms sharedDivisorPairs_card_real_le
#print axioms largePrimeNoncoprimePairs_card_real_le

end Erdos883Second.Link
