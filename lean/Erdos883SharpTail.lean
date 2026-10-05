import Erdos883TailDensity
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

/-- The natural Euler factor is nonnegative above one. -/
theorem eulerFactor_nonneg {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ 1 - (p : ℚ)⁻¹ := by
  have hp0 : (0 : ℚ) < p := Nat.cast_pos.mpr (by omega)
  have heq : ((p : ℚ) - 1) / p = 1 - (p : ℚ)⁻¹ := by
    rw [sub_div, div_self hp0.ne', one_div]
  rw [← heq]
  exact (thresholdFactor_mem_unitInterval hp).1

/-- Euler factors increase with their positive natural argument. -/
theorem eulerFactor_mono {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    1 - (p : ℚ)⁻¹ ≤ 1 - (q : ℚ)⁻¹ := by
  have hp0 : (0 : ℚ) < p := Nat.cast_pos.mpr (by omega)
  exact sub_le_sub_left (inv_anti₀ hp0 (Nat.cast_le.mpr hpq)) 1

/-- A sharp Euler-product comparison. The benchmark `Q` need not consist of
primes: its entries lie between two and the threshold, all new entries in `S`
are at least the threshold, and `S` has no more entries than `Q`. -/
theorem finset_euler_product_comparison (S Q : Finset ℕ) {q : ℕ}
    (hq : 2 ≤ q) (hS : ∀ x ∈ S, 2 ≤ x)
    (hQ : ∀ x ∈ Q, 2 ≤ x) (hsmall : ∀ x ∈ Q, x ≤ q)
    (hlarge : ∀ x ∈ S, x ∉ Q → q ≤ x)
    (hcard : S.card ≤ Q.card) :
    (∏ x ∈ Q, (1 - (x : ℚ)⁻¹)) ≤ ∏ x ∈ S, (1 - (x : ℚ)⁻¹) := by
  have hc : (S \ Q).card ≤ (Q \ S).card := by
    have hS' := Finset.card_sdiff_add_card_inter S Q
    have hQ' := Finset.card_sdiff_add_card_inter Q S
    rw [Finset.inter_comm Q S] at hQ'
    omega
  let c : ℚ := 1 - (q : ℚ)⁻¹
  have hc0 : 0 ≤ c := eulerFactor_nonneg hq
  have hc1 : c ≤ 1 := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg q))
  have hsmallprod : (∏ x ∈ Q \ S, (1 - (x : ℚ)⁻¹)) ≤ c ^ (Q \ S).card := by
    calc
      _ ≤ ∏ _x ∈ Q \ S, c := Finset.prod_le_prod
        (fun x hx => eulerFactor_nonneg (hQ x (Finset.mem_sdiff.mp hx).1))
        (fun x hx => eulerFactor_mono (hQ x (Finset.mem_sdiff.mp hx).1)
          (hsmall x (Finset.mem_sdiff.mp hx).1))
      _ = _ := by rw [Finset.prod_const]
  have hlargeprod : c ^ (S \ Q).card ≤ ∏ x ∈ S \ Q, (1 - (x : ℚ)⁻¹) := by
    calc
      _ = ∏ _x ∈ S \ Q, c := by rw [Finset.prod_const]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hc0)
        (fun x hx => eulerFactor_mono hq
          (hlarge x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2))
  have hfactor : (∏ x ∈ Q \ S, (1 - (x : ℚ)⁻¹)) ≤
      ∏ x ∈ S \ Q, (1 - (x : ℚ)⁻¹) :=
    hsmallprod.trans ((pow_le_pow_of_le_one hc0 hc1 hc).trans hlargeprod)
  calc
    _ = (∏ x ∈ S ∩ Q, (1 - (x : ℚ)⁻¹)) *
        (∏ x ∈ Q \ S, (1 - (x : ℚ)⁻¹)) := by
      rw [← Finset.prod_inter_mul_prod_sdiff Q S (fun x : ℕ => 1 - (x : ℚ)⁻¹),
        Finset.inter_comm Q S]
    _ ≤ (∏ x ∈ S ∩ Q, (1 - (x : ℚ)⁻¹)) *
        (∏ x ∈ S \ Q, (1 - (x : ℚ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hfactor (Finset.prod_nonneg
        (fun x hx => eulerFactor_nonneg (hS x (Finset.mem_inter.mp hx).1)))
    _ = _ := Finset.prod_inter_mul_prod_sdiff S Q (fun x : ℕ => 1 - (x : ℚ)⁻¹)

/-- A small product certificate gives the benchmark cardinality bound for the
prime factors introduced by an odd second endpoint. -/
theorem missingPrime_card_le_of_signature_product_barrier
    (Q : Finset ℕ) {u v U q : ℕ} {ps : List ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v) (hvU : v ≤ U)
    (hq : 2 ≤ q) (hsmall : ∀ x ∈ Q, x ≤ q)
    (hcover : ∀ r, r.Prime → Odd r → r < q → r ∈ ps ∨ r ∈ Q)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v)
    (hbudget : U < q * (∏ x ∈ Q, x)) :
    (v.primeFactors \ u.primeFactors).card ≤ Q.card := by
  have hlarge : ∀ r ∈ v.primeFactors \ u.primeFactors, r ∉ Q → q ≤ r := by
    intro r hr hrQ
    rcases Finset.mem_sdiff.mp hr with ⟨hrv, hru⟩
    by_contra hrq
    have hrprime := Nat.prime_of_mem_primeFactors hrv
    have hrps : r ∈ ps := (hcover r hrprime
      (hvodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hrv)) (by omega)).resolve_right hrQ
    have hd : r ∣ u := (divisorSignatureCode_eq_imp_dvd_iff ps u v hcode hrps).mpr
      (Nat.dvd_of_mem_primeFactors hrv)
    exact hru ((Nat.mem_primeFactors_of_ne_zero hu.ne').mpr ⟨hrprime, hd⟩)
  by_contra hcard
  have hbarrier := finset_product_barrier (v.primeFactors \ u.primeFactors) Q
    (by omega : 1 ≤ q) hsmall hlarge (by omega)
  have hprod : (∏ r ∈ v.primeFactors \ u.primeFactors, r) ≤ v :=
    Nat.le_of_dvd hv (prod_primeFactors_subset_dvd Finset.sdiff_subset)
  omega

/-- Sharp primorial-tail preservation. Benchmark entries need not be prime,
but must be at least two and at most `q`. Coverage only concerns odd primes
below `q`; listed signature coordinates account for the other small primes. -/
theorem totientDensity_lcm_ge_signature_sharpTail
    (Q : Finset ℕ) {u v U q : ℕ} {ps : List ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v) (hvU : v ≤ U)
    (hq : 2 ≤ q) (hQ : ∀ x ∈ Q, 2 ≤ x) (hsmall : ∀ x ∈ Q, x ≤ q)
    (hcover : ∀ r, r.Prime → Odd r → r < q → r ∈ ps ∨ r ∈ Q)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v)
    (hbudget : U < q * (∏ x ∈ Q, x)) :
    totientDensity u * (∏ x ∈ Q, (1 - (x : ℚ)⁻¹)) ≤
      totientDensity (Nat.lcm u v) := by
  rw [totientDensity_lcm_eq_mul_prod_sdiff hu hv]
  apply mul_le_mul_of_nonneg_left _ (totientDensity_nonneg u)
  apply finset_euler_product_comparison _ Q hq
    (fun r hr => (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hr).1).two_le)
    hQ hsmall ?_
    (missingPrime_card_le_of_signature_product_barrier Q hu hv hvodd hvU hq
      hsmall hcover hcode hbudget)
  intro r hr hrQ
  rcases Finset.mem_sdiff.mp hr with ⟨hrv, hru⟩
  by_contra hrq
  have hrprime := Nat.prime_of_mem_primeFactors hrv
  have hrps : r ∈ ps := (hcover r hrprime
    (hvodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hrv)) (by omega)).resolve_right hrQ
  have hd : r ∣ u := (divisorSignatureCode_eq_imp_dvd_iff ps u v hcode hrps).mpr
    (Nat.dvd_of_mem_primeFactors hrv)
  exact hru ((Nat.mem_primeFactors_of_ne_zero hu.ne').mpr ⟨hrprime, hd⟩)

/-- The sharp tail comparison for equal binary prefixes of a longer signature. -/
theorem totientDensity_lcm_ge_prefix_sharpTail
    (Q : Finset ℕ) {u v U q s : ℕ} {ps : List ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v) (hvU : v ≤ U)
    (hq : 2 ≤ q) (hQ : ∀ x ∈ Q, 2 ≤ x) (hsmall : ∀ x ∈ Q, x ≤ q)
    (hcover : ∀ r, r.Prime → Odd r → r < q → r ∈ ps.take s ∨ r ∈ Q)
    (hcode : divisorSignatureCode ps u / 2 ^ (ps.length - s) =
      divisorSignatureCode ps v / 2 ^ (ps.length - s))
    (hbudget : U < q * (∏ x ∈ Q, x)) :
    totientDensity u * (∏ x ∈ Q, (1 - (x : ℚ)⁻¹)) ≤
      totientDensity (Nat.lcm u v) := by
  apply totientDensity_lcm_ge_signature_sharpTail Q hu hv hvodd hvU hq hQ hsmall
    hcover ?_ hbudget
  simpa only [divisorSignatureCode_take] using hcode

/-- A fully finite coverage check is enough for the sharp signature-tail bound. -/
theorem totientDensity_lcm_ge_finite_signature_sharpTail
    (Q : Finset ℕ) {u v U q : ℕ} {ps : List ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v) (hvU : v ≤ U)
    (hq : 2 ≤ q) (hQ : ∀ x ∈ Q, 2 ≤ x) (hsmall : ∀ x ∈ Q, x ≤ q)
    (hcover : ∀ r ∈ Finset.range q, r.Prime → r % 2 = 1 → r ∈ ps ∨ r ∈ Q)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v)
    (hbudget : U < q * (∏ x ∈ Q, x)) :
    totientDensity u * (∏ x ∈ Q, (1 - (x : ℚ)⁻¹)) ≤
      totientDensity (Nat.lcm u v) := by
  exact totientDensity_lcm_ge_signature_sharpTail Q hu hv hvodd hvU hq hQ hsmall
    (fun r hp ho hlt => hcover r (Finset.mem_range.mpr hlt) hp (Nat.odd_iff.mp ho))
    hcode hbudget

end Erdos883Verified

#print axioms Erdos883Verified.finset_euler_product_comparison
#print axioms Erdos883Verified.missingPrime_card_le_of_signature_product_barrier
#print axioms Erdos883Verified.totientDensity_lcm_ge_signature_sharpTail
#print axioms Erdos883Verified.totientDensity_lcm_ge_prefix_sharpTail
#print axioms Erdos883Verified.totientDensity_lcm_ge_finite_signature_sharpTail
