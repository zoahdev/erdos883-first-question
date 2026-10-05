import Erdos883PrimeBasisCore
import Erdos883AdaptiveCertificateProfiles
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Erdos883Verified

theorem corePrimeCheck_of_prime {p : ℕ} (hp : p.Prime) : corePrimeCheck p = true := by
  simp only [corePrimeCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hp.two_le, List.all_eq_true.mpr ?_⟩
  intro d hd
  apply decide_eq_true_eq.mpr
  by_cases hd2 : d < 2
  · exact Or.inl hd2
  · apply Or.inr
    intro hmod
    exact (Nat.prime_def_le_sqrt.mp hp).2 d (by omega)
      (by have := List.mem_range.mp hd; omega) (Nat.dvd_of_mod_eq_zero hmod)

theorem smallPrimeTrialBasis_check :
    ∀ q : Fin 448, corePrimeCheck q.val = true → q.val ∈ smallPrimeTrialBasis := by decide +kernel

theorem smallPrimeTrialBasis_complete (q : Fin 448) (hq : q.val.Prime) :
    q.val ∈ smallPrimeTrialBasis :=
  smallPrimeTrialBasis_check q (corePrimeCheck_of_prime hq)

theorem coreBasisPrimeCheck_sound {p : ℕ} (h : coreBasisPrimeCheck p = true) : p.Prime := by
  simp only [coreBasisPrimeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨h.1.1, ?_⟩
  intro d hd hdsqrt hdp
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hqle : q ≤ d := Nat.le_of_dvd (by omega) hqd
  have hqsqrt : q ≤ Nat.sqrt p := hqle.trans hdsqrt
  have hsqrt : Nat.sqrt p ≤ 447 := by
    have hs : Nat.sqrt p < 448 := Nat.sqrt_lt.mpr (by omega)
    omega
  have hmem := smallPrimeTrialBasis_complete ⟨q, by omega⟩ hq
  have htest := of_decide_eq_true (List.all_eq_true.mp h.2 q hmem)
  have hqq : q*q ≤ p := Nat.le_sqrt.mp hqsqrt
  have hmod : p % q = 0 := Nat.mod_eq_zero_of_dvd (hqd.trans hdp)
  omega

theorem coreBasisProfileRowCheck_sound {row : AdaptiveProfileRow}
    (h : coreBasisProfileRowCheck row = true) : row.Valid := by
  simp only [coreBasisProfileRowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  rw [h.2.2.2, coreDedup_eq, corePrimeSieveCount_eq]
  apply fastPrimeSieveCount_factorList_eq_totient h.1 h.2.1
  intro p hp
  exact coreBasisPrimeCheck_sound (List.all_eq_true.mp h.2.2.1 p hp)

theorem coreBasisProfileMetadataCheck_sound {rows : List AdaptiveProfileRow}
    (h : coreBasisProfileMetadataCheck rows = true) : AdaptiveProfileRowsValid rows := by
  intro row hrow
  exact coreBasisProfileRowCheck_sound (List.all_eq_true.mp h row hrow)

theorem coreProfileRowCheck_of_basis {row : AdaptiveProfileRow}
    (h : coreBasisProfileRowCheck row = true) : coreProfileRowCheck row = true := by
  simp only [coreBasisProfileRowCheck, Bool.and_eq_true] at h
  simp only [coreProfileRowCheck, Bool.and_eq_true]
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  apply List.all_eq_true.mpr
  intro p hp
  exact corePrimeCheck_of_prime (coreBasisPrimeCheck_sound (List.all_eq_true.mp h.2.2.1 p hp))

theorem coreProfileMetadataCheck_of_basis {rows : List AdaptiveProfileRow}
    (h : coreBasisProfileMetadataCheck rows = true) : coreProfileMetadataCheck rows = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  exact coreProfileRowCheck_of_basis (List.all_eq_true.mp h row hrow)

#print axioms coreProfileMetadataCheck_of_basis
#print axioms smallPrimeTrialBasis_complete
#print axioms coreBasisPrimeCheck_sound
#print axioms coreBasisProfileMetadataCheck_sound
end Erdos883Verified
