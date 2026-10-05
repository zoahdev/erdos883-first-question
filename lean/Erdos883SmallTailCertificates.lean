import Erdos883UniformTail
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

/-- A cardinality bound from a single exact power barrier. -/
theorem finset_card_le_of_power_barrier {S : Finset ℕ} {p a U : ℕ}
    (hp : 1 ≤ p) (hsmall : ∀ q ∈ S, p ≤ q)
    (hprod : (∏ q ∈ S, q) ≤ U) (hbarrier : U < p ^ (a + 1)) : S.card ≤ a := by
  have hpow : p ^ S.card ≤ U := by
    calc
      p ^ S.card = ∏ _q ∈ S, p := by simp
      _ ≤ ∏ q ∈ S, q := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hsmall
      _ ≤ U := hprod
  by_contra h
  have hcard : a + 1 ≤ S.card := by omega
  have hle := pow_le_pow_right' hp hcard
  omega

/-- There is no prime strictly between nineteen and twenty-three. -/
theorem prime_ge_twenty_three {p : ℕ} (hp : p.Prime) (h19 : 19 ≤ p) (hne : p ≠ 19) :
    23 ≤ p := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hmod := Nat.odd_iff.mp hodd
  by_contra h
  have heq : p = 21 := by omega
  subst p
  exact absurd hp (by decide)

/-- Every prime at least twenty-three and less than thirty-one is 23 or 29. -/
theorem prime_ge_thirty_one_or_mem {p : ℕ} (hp : p.Prime) (h23 : 23 ≤ p) :
    31 ≤ p ∨ p ∈ ({23, 29} : Finset ℕ) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hmod := Nat.odd_iff.mp hodd
  by_cases h31 : 31 ≤ p
  · exact Or.inl h31
  · have heq : p = 23 ∨ p = 25 ∨ p = 27 ∨ p = 29 := by omega
    rcases heq with rfl | rfl | rfl | rfl <;> norm_num at *
    all_goals exact absurd hp (by decide)

/-- The small scale `s=6`: distinctness improves the threshold 19 estimate. -/
theorem primeFinset_tailFactor_gt_nine_tenths_scale_six {S : Finset ℕ}
    (hprime : ∀ q ∈ S, q.Prime) (hsmall : ∀ q ∈ S, 19 ≤ q)
    (hprod : (∏ q ∈ S, q) ≤ 4 ^ 6) :
    (9 / 10 : ℚ) < ∏ q ∈ S, (1 - (q : ℚ)⁻¹) := by
  have hcard : S.card ≤ 2 := finset_card_le_of_power_barrier (by decide) hsmall hprod (by norm_num)
  by_cases h19 : 19 ∈ S
  · have hcard' : (S.erase 19).card ≤ 1 := by
      have h := Finset.card_erase_add_one h19
      omega
    have hsmall' : ∀ q ∈ S.erase 19, 23 ≤ q := by
      intro q hq
      obtain ⟨hq19, hqS⟩ := Finset.mem_erase.mp hq
      exact prime_ge_twenty_three (hprime q hqS) (hsmall q hqS) hq19
    have hfac : (22 / 23 : ℚ) ≤ ∏ q ∈ S.erase 19, (1 - (q : ℚ)⁻¹) := by
      calc
        (22 / 23 : ℚ) = (((23 : ℚ) - 1) / 23) ^ 1 := by norm_num
        _ ≤ (((23 : ℚ) - 1) / 23) ^ (S.erase 19).card :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard'
        _ ≤ _ := thresholdFactor_pow_card_le_prod (by decide) hsmall'
    have heq : (∏ q ∈ S, (1 - (q : ℚ)⁻¹)) =
        (1 - (19 : ℚ)⁻¹) * ∏ q ∈ S.erase 19, (1 - (q : ℚ)⁻¹) :=
      (Finset.mul_prod_erase _ _ h19).symm
    rw [heq]
    norm_num at *
    linarith
  · have hsmall' : ∀ q ∈ S, 23 ≤ q := by
      intro q hq
      exact prime_ge_twenty_three (hprime q hq) (hsmall q hq) (by aesop)
    have hfac := thresholdFactor_pow_card_le_prod (by decide : 2 ≤ 23) hsmall'
    have hpow : (((23 : ℚ) - 1) / 23) ^ 2 ≤
        (((23 : ℚ) - 1) / 23) ^ S.card :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
    exact lt_of_lt_of_le (by norm_num) (hpow.trans hfac)

/-- The small scale `s=7`: three distinct missing primes exceed the size cap. -/
theorem primeFinset_tailFactor_gt_nine_tenths_scale_seven {S : Finset ℕ}
    (hprime : ∀ q ∈ S, q.Prime) (hsmall : ∀ q ∈ S, 23 ≤ q)
    (hprod : (∏ q ∈ S, q) ≤ 4 ^ 7) :
    (9 / 10 : ℚ) < ∏ q ∈ S, (1 - (q : ℚ)⁻¹) := by
  have hcard : S.card ≤ 2 := by
    by_contra h
    have hbarrier := finset_product_barrier S {23, 29} (by decide : 1 ≤ 31)
      (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> decide)
      (by intro p hp hn
          exact (prime_ge_thirty_one_or_mem (hprime p hp) (hsmall p hp)).resolve_right hn)
      (by norm_num; omega)
    norm_num at hbarrier hprod
    omega
  have hfac := thresholdFactor_pow_card_le_prod (by decide : 2 ≤ 23) hsmall
  have hpow : (((23 : ℚ) - 1) / 23) ^ 2 ≤
      (((23 : ℚ) - 1) / 23) ^ S.card :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
  exact lt_of_lt_of_le (by norm_num) (hpow.trans hfac)

/-- The small scale `s=8`: the exact cubic inequality beats Bernoulli. -/
theorem primeFinset_tailFactor_gt_nine_tenths_scale_eight {S : Finset ℕ}
    (hsmall : ∀ q ∈ S, 29 ≤ q) (hprod : (∏ q ∈ S, q) ≤ 4 ^ 8) :
    (9 / 10 : ℚ) < ∏ q ∈ S, (1 - (q : ℚ)⁻¹) := by
  have hcard : S.card ≤ 3 := finset_card_le_of_power_barrier (by decide) hsmall hprod (by norm_num)
  have hfac := thresholdFactor_pow_card_le_prod (by decide : 2 ≤ 29) hsmall
  have hpow : (((29 : ℚ) - 1) / 29) ^ 3 ≤
      (((29 : ℚ) - 1) / 29) ^ S.card :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
  exact lt_of_lt_of_le (by norm_num) (hpow.trans hfac)

end Erdos883Verified
#print axioms Erdos883Verified.finset_card_le_of_power_barrier
#print axioms Erdos883Verified.prime_ge_twenty_three
#print axioms Erdos883Verified.prime_ge_thirty_one_or_mem
#print axioms Erdos883Verified.primeFinset_tailFactor_gt_nine_tenths_scale_six
#print axioms Erdos883Verified.primeFinset_tailFactor_gt_nine_tenths_scale_seven
#print axioms Erdos883Verified.primeFinset_tailFactor_gt_nine_tenths_scale_eight
