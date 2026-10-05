import Erdos883CoprimeDiscrepancy

namespace Erdos883Verified

open Finset

/-- A finite product barrier: all omitted benchmark factors are at most `q`,
while every new factor is at least `q`. One extra factor forces the product
above `q` times the benchmark product. -/
theorem finset_product_barrier (S P : Finset ℕ) {q : ℕ}
    (hq : 1 ≤ q) (hsmall : ∀ p ∈ P, p ≤ q)
    (hlarge : ∀ x ∈ S, x ∉ P → q ≤ x)
    (hcard : P.card + 1 ≤ S.card) :
    q * (∏ p ∈ P, p) ≤ ∏ x ∈ S, x := by
  have hc : (P \ S).card + 1 ≤ (S \ P).card := by
    have hS := Finset.card_sdiff_add_card_inter S P
    have hP := Finset.card_sdiff_add_card_inter P S
    rw [Finset.inter_comm P S] at hP
    omega
  have hsmallprod : (∏ p ∈ P \ S, p) ≤ q ^ (P \ S).card := by
    calc
      (∏ p ∈ P \ S, p) ≤ ∏ _p ∈ P \ S, q := by
        exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp =>
          hsmall p (Finset.mem_sdiff.mp hp).1)
      _ = q ^ (P \ S).card := by simp
  have hlargeprod : q ^ (S \ P).card ≤ ∏ x ∈ S \ P, x := by
    calc
      q ^ (S \ P).card = ∏ _x ∈ S \ P, q := by simp
      _ ≤ ∏ x ∈ S \ P, x := by
        exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun x hx =>
          hlarge x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2)
  have hfactor : q * (∏ p ∈ P \ S, p) ≤ ∏ x ∈ S \ P, x := by
    calc
      q * (∏ p ∈ P \ S, p) ≤ q * q ^ (P \ S).card :=
        Nat.mul_le_mul_left q hsmallprod
      _ = q ^ ((P \ S).card + 1) := by rw [pow_succ, Nat.mul_comm]
      _ ≤ q ^ (S \ P).card := pow_le_pow_right' hq hc
      _ ≤ ∏ x ∈ S \ P, x := hlargeprod
  calc
    q * (∏ p ∈ P, p) = (∏ x ∈ S ∩ P, x) *
        (q * (∏ p ∈ P \ S, p)) := by
      rw [← Finset.prod_inter_mul_prod_sdiff P S (fun x : ℕ => x), Finset.inter_comm P S]
      ring
    _ ≤ (∏ x ∈ S ∩ P, x) * (∏ x ∈ S \ P, x) :=
      Nat.mul_le_mul_left _ hfactor
    _ = ∏ x ∈ S, x := Finset.prod_inter_mul_prod_sdiff S P (fun x : ℕ => x)

/-- A product threshold bounds the number of distinct prime divisors of a
positive odd integer. `P` need only cover every odd prime below `q`; the
benchmark product may be checked separately by finite computation. -/
theorem odd_primeFactors_card_le_of_product_barrier (P : Finset ℕ) {q n B : ℕ}
    (hq : 2 ≤ q) (hsmall : ∀ p ∈ P, p ≤ q)
    (hcover : ∀ p : ℕ, p.Prime → Odd p → p < q → p ∈ P)
    (hn : 0 < n) (hnodd : Odd n) (hnB : n ≤ B)
    (hbudget : B < q * (∏ p ∈ P, p)) :
    n.primeFactors.card ≤ P.card := by
  by_contra h
  have hcard : P.card + 1 ≤ n.primeFactors.card := by omega
  have hbarrier := finset_product_barrier n.primeFactors P (by omega : 1 ≤ q)
    hsmall (by
      intro p hp hnot
      by_contra hlt
      exact hnot (hcover p (Nat.prime_of_mem_primeFactors hp)
        (hnodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)) (by omega))) hcard
  have hprod : (∏ p ∈ n.primeFactors, p) ≤ n :=
    Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  omega

/-- Primorial support budget for the lcm of two positive odd endpoints at most `U`. -/
theorem odd_lcm_primeFactors_card_le_of_product_barrier
    (P : Finset ℕ) {q u v U : ℕ}
    (hq : 2 ≤ q) (hsmall : ∀ p ∈ P, p ≤ q)
    (hcover : ∀ p : ℕ, p.Prime → Odd p → p < q → p ∈ P)
    (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v)
    (huU : u ≤ U) (hvU : v ≤ U)
    (hbudget : U ^ 2 < q * (∏ p ∈ P, p)) :
    (Nat.lcm u v).primeFactors.card ≤ P.card := by
  apply odd_primeFactors_card_le_of_product_barrier P hq hsmall hcover
    (Nat.lcm_pos hu hv)
    ((huodd.mul hvodd).of_dvd_nat (Nat.lcm_dvd_mul u v)) ?_ hbudget
  calc
    Nat.lcm u v ≤ u * v := Nat.lcm_le_mul hu hv
    _ ≤ U * U := Nat.mul_le_mul huU hvU
    _ = U ^ 2 := by ring

/-- A finite, decidable form of the prime-coverage hypothesis. -/
theorem odd_lcm_primeFactors_card_le_of_finite_product_barrier
    (P : Finset ℕ) {q u v U : ℕ}
    (hq : 2 ≤ q) (hsmall : ∀ p ∈ P, p ≤ q)
    (hcover : ∀ p ∈ Finset.range q, p.Prime → p % 2 = 1 → p ∈ P)
    (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v)
    (huU : u ≤ U) (hvU : v ≤ U)
    (hbudget : U ^ 2 < q * (∏ p ∈ P, p)) :
    (Nat.lcm u v).primeFactors.card ≤ P.card := by
  exact odd_lcm_primeFactors_card_le_of_product_barrier P hq hsmall
    (fun p hp ho hlt => hcover p (Finset.mem_range.mpr hlt) hp (Nat.odd_iff.mp ho))
    hu hv huodd hvodd huU hvU hbudget

/-- The canonical computable benchmark: all odd primes below the threshold. -/
def oddPrimeBenchmark (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun p => p.Prime ∧ p % 2 = 1)

@[simp] theorem mem_oddPrimeBenchmark {p q : ℕ} :
    p ∈ oddPrimeBenchmark q ↔ p < q ∧ p.Prime ∧ Odd p := by
  simp [oddPrimeBenchmark, Nat.odd_iff]

/-- A canonical primorial threshold supplies the support budget without a separate
coverage proof. The numerical hypothesis and benchmark cardinality are decidable. -/
theorem odd_lcm_primeFactors_card_le_benchmark {q u v U : ℕ}
    (hq : 2 ≤ q)
    (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v)
    (huU : u ≤ U) (hvU : v ≤ U)
    (hbudget : U ^ 2 < q * (∏ p ∈ oddPrimeBenchmark q, p)) :
    (Nat.lcm u v).primeFactors.card ≤ (oddPrimeBenchmark q).card := by
  exact odd_lcm_primeFactors_card_le_of_product_barrier (oddPrimeBenchmark q) hq
    (fun p hp => (mem_oddPrimeBenchmark.mp hp).1.le)
    (fun p hp ho hlt => mem_oddPrimeBenchmark.mpr ⟨hlt, hp, ho⟩)
    hu hv huodd hvodd huU hvU hbudget

end Erdos883Verified

#print axioms Erdos883Verified.finset_product_barrier
#print axioms Erdos883Verified.odd_primeFactors_card_le_of_product_barrier
#print axioms Erdos883Verified.odd_lcm_primeFactors_card_le_of_product_barrier

#print axioms Erdos883Verified.odd_lcm_primeFactors_card_le_of_finite_product_barrier
#print axioms Erdos883Verified.mem_oddPrimeBenchmark
#print axioms Erdos883Verified.odd_lcm_primeFactors_card_le_benchmark
