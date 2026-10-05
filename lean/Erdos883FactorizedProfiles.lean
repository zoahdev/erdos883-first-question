import Erdos883AdaptiveHistogram
import Erdos883SmallCertificateCoreBridge

namespace Erdos883Verified

/-- An explicitly supplied factor list is checked before it is used for a profile. -/
theorem primeFactors_eq_factorList {n : ℕ} {ps : List ℕ}
    (hprod : ps.prod = n) (hp : ∀ p ∈ ps, Nat.Prime p) :
    n.primeFactors = ps.toFinset := by
  ext p
  simpa only [Nat.primeFactors, List.mem_toFinset] using
    ((Nat.primeFactorsList_unique hprod hp).mem_iff (a := p)).symm

/-- Exact Euler profile from a certified factorization, including repeated prime factors. -/
theorem totientDensity_eq_factorList {n : ℕ} {ps : List ℕ}
    (hn : 0 < n) (hprod : ps.prod = n) (hp : ∀ p ∈ ps, Nat.Prime p) :
    totientDensity n = ((ps.dedup.map (fun p : ℕ => 1 - (p : ℚ)⁻¹)).prod) := by
  rw [totientDensity_eq_prod hn, primeFactors_eq_factorList hprod hp]
  have hd : ps.dedup.toFinset = ps.toFinset := by ext p; simp
  rw [← hd, List.prod_toFinset _ (List.nodup_dedup ps)]

/-- The floor-division sieve at one complete period computes Euler's totient. -/
theorem coprimePrefixCount_self_eq_totient (n : ℕ) :
    coprimePrefixCount n n = Nat.totient n := by
  rw [coprimePrefixCount]
  convert Nat.filter_coprime_Ico_eq_totient n 1 using 2 <;>
    ext x <;> simp [Nat.coprime_comm] <;> omega

/-- A numeric totient numerator certified using only a small prime support. -/
theorem fastPrimeSieveCount_factorList_eq_totient {n : ℕ} {ps : List ℕ}
    (hn : 0 < n) (hprod : ps.prod = n) (hp : ∀ p ∈ ps, Nat.Prime p) :
    fastPrimeSieveCount n ps.dedup = Nat.totient n := by
  rw [fastPrimeSieveCount_eq_coprimePrefixCount_of_primeFactors n hn
    (List.nodup_dedup ps) (by
      rw [primeFactors_eq_factorList hprod hp]
      ext p; simp)]
  exact coprimePrefixCount_self_eq_totient n

#print axioms primeFactors_eq_factorList
#print axioms totientDensity_eq_factorList
#print axioms coprimePrefixCount_self_eq_totient
#print axioms fastPrimeSieveCount_factorList_eq_totient
end Erdos883Verified
