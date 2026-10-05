import Erdos883NeighborDiscrepancy
import Mathlib.Data.Nat.GCD.BigOperators

namespace Erdos883Verified

/-- Inclusion-exclusion by the list of distinct prime divisors, using only floor divisions. -/
def fastPrimeSieveCount (X : ℕ) : List ℕ → ℕ
  | [] => X
  | p :: ps => fastPrimeSieveCount X ps - fastPrimeSieveCount (X / p) ps

/-- The multiples of a coprime factor in a positive coprime prefix are a scaling image. -/
theorem coprimePrefix_multiples_eq_image (X : ℕ) {p d : ℕ}
    (hp : 0 < p) (hpd : Nat.Coprime p d) :
    ((Finset.Icc 1 X).filter (fun w => Nat.Coprime w d)).filter (fun w => p ∣ w) =
      ((Finset.Icc 1 (X / p)).filter (fun w => Nat.Coprime w d)).image (fun w => p * w) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨hwlo, hwhi⟩, hwcop⟩, ⟨k, rfl⟩⟩
    refine ⟨k, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
    · by_contra h
      have hk : k = 0 := by omega
      simp [hk] at hwlo
    · exact (Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using hwhi)
    · exact (Nat.coprime_mul_iff_left.mp hwcop).2
  · rintro ⟨k, ⟨⟨hklo, hkhi⟩, hkcop⟩, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, hpd.mul_left hkcop⟩, dvd_mul_right p k⟩
    · exact Nat.succ_le_of_lt (Nat.mul_pos hp (by omega))
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hkhi

/-- Sieving out one new prime subtracts the scaled coprime prefix exactly. -/
theorem coprimePrefixCount_prime_mul (X : ℕ) {p d : ℕ}
    (hp : Nat.Prime p) (hpd : Nat.Coprime p d) :
    coprimePrefixCount X (p * d) =
      coprimePrefixCount X d - coprimePrefixCount (X / p) d := by
  have hmul : (((Finset.Icc 1 X).filter (fun w => Nat.Coprime w d)).filter
      (fun w => p ∣ w)).card = coprimePrefixCount (X / p) d := by
    rw [coprimePrefix_multiples_eq_image X hp.pos hpd]
    apply Finset.card_image_of_injective
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  have hnot : ((Finset.Icc 1 X).filter (fun w => Nat.Coprime w d)).filter
      (fun w => ¬ p ∣ w) =
      (Finset.Icc 1 X).filter (fun w => Nat.Coprime w (p * d)) := by
    ext w
    simp only [Finset.mem_filter, Nat.coprime_mul_iff_right]
    rw [Nat.coprime_comm (n := w) (m := p), hp.coprime_iff_not_dvd]
    tauto
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.Icc 1 X).filter (fun w => Nat.Coprime w d)) (p := fun w => p ∣ w)
  rw [hmul, hnot] at hsum
  change coprimePrefixCount (X / p) d + coprimePrefixCount X (p * d) =
    coprimePrefixCount X d at hsum
  omega

/-- Exactness of the floor-division sieve for a nodup list of primes. -/
theorem fastPrimeSieveCount_eq_coprimePrefixCount (X : ℕ) {ps : List ℕ}
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, Nat.Prime p) :
    fastPrimeSieveCount X ps = coprimePrefixCount X ps.prod := by
  induction ps generalizing X with
  | nil => simp [fastPrimeSieveCount, coprimePrefixCount]
  | cons p ps ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hnd
    have hprime : Nat.Prime p := hp p (by simp)
    have htail : ∀ q ∈ ps, Nat.Prime q := fun q hq => hp q (by simp [hq])
    have hcop : Nat.Coprime p ps.prod := by
      apply Nat.coprime_list_prod_right_iff.mpr
      intro q hq
      exact (hprime.coprime_iff_not_dvd).mpr (by
        intro hdvd
        have heq := (Nat.dvd_prime (htail q hq)).mp hdvd
        rcases heq with heq | heq
        · exact hprime.ne_one heq
        · exact hnot (heq ▸ hq))
    rw [fastPrimeSieveCount, List.prod_cons, ih X hnd htail,
      ih (X / p) hnd htail, coprimePrefixCount_prime_mul X hprime hcop]

/-- Supplying precisely the prime support computes the count for any positive modulus. -/
theorem fastPrimeSieveCount_eq_coprimePrefixCount_of_primeFactors
    (X : ℕ) {d : ℕ} {ps : List ℕ} (hd : 0 < d) (hnd : ps.Nodup)
    (hset : ps.toFinset = d.primeFactors) :
    fastPrimeSieveCount X ps = coprimePrefixCount X d := by
  have hp : ∀ p ∈ ps, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (hset ▸ List.mem_toFinset.mpr hp)
  rw [fastPrimeSieveCount_eq_coprimePrefixCount X hnd hp]
  have hprod : ps.prod = UniqueFactorizationMonoid.radical d := by
    rw [Nat.radical_eq_prod_primeFactors, ← hset, List.prod_toFinset _ hnd]
    simp
  rw [hprod, coprimePrefixCount_radical X hd]

/-- A divisor and a reverse power-divisor certify identical prime supports without
computing either prime-factor finsets or radicals. -/
theorem fastPrimeSieveCount_eq_coprimePrefixCount_of_dvd_pow
    (X : ℕ) {d k : ℕ} {ps : List ℕ} (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, Nat.Prime p) (hpd : ps.prod ∣ d) (hdp : d ∣ ps.prod ^ k) :
    fastPrimeSieveCount X ps = coprimePrefixCount X d := by
  rw [fastPrimeSieveCount_eq_coprimePrefixCount X hnd hp]
  unfold coprimePrefixCount
  congr 1
  apply Finset.filter_congr
  intro w hw
  exact ⟨fun h => (h.pow_right k).of_dvd_right hdp, fun h => h.of_dvd_right hpd⟩

/-- For lower bounds it suffices that the supplied prime list covers the modulus.
Extra distinct primes in the list are harmless, and no factorization is evaluated. -/
theorem fastPrimeSieveCount_le_coprimePrefixCount_of_dvd_pow
    (X : ℕ) {d k : ℕ} {ps : List ℕ} (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, Nat.Prime p) (hdp : d ∣ ps.prod ^ k) :
    fastPrimeSieveCount X ps ≤ coprimePrefixCount X d := by
  rw [fastPrimeSieveCount_eq_coprimePrefixCount X hnd hp]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hw, hcop⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨hw, (hcop.pow_right k).of_dvd_right hdp⟩

#print axioms fastPrimeSieveCount_eq_coprimePrefixCount_of_dvd_pow
#print axioms fastPrimeSieveCount_le_coprimePrefixCount_of_dvd_pow

#print axioms fastPrimeSieveCount
#print axioms coprimePrefix_multiples_eq_image
#print axioms coprimePrefixCount_prime_mul
#print axioms fastPrimeSieveCount_eq_coprimePrefixCount
#print axioms fastPrimeSieveCount_eq_coprimePrefixCount_of_primeFactors

end Erdos883Verified
