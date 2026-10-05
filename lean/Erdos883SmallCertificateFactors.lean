import Erdos883SmallCertificateFastCount
import Erdos883CoprimeCounts
import Mathlib.Data.Nat.GCD.BigOperators
namespace Erdos883Verified

theorem coprime_dedup_append_prod_iff (w : ℕ) (pu pv : List ℕ) :
    Nat.Coprime w ((pu ++ pv).dedup.prod) ↔
      Nat.Coprime w pu.prod ∧ Nat.Coprime w pv.prod := by
  simp only [Nat.coprime_list_prod_right_iff, List.mem_dedup, List.mem_append]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨hu, hv⟩ p (hp | hp)
    · exact hu p hp
    · exact hv p hp

theorem coprimePrefixCount_dedup_append_prod (X : ℕ) {pu pv : List ℕ} {u v : ℕ}
    (hu : pu.prod = u) (hv : pv.prod = v) :
    coprimePrefixCount X ((pu ++ pv).dedup.prod) =
      coprimePrefixCount X (Nat.lcm u v) := by
  unfold coprimePrefixCount
  congr 1
  ext w
  simp only [Finset.mem_filter, coprime_dedup_append_prod_iff, hu, hv, coprime_lcm_iff]

theorem factorized_rawCommon_card (L : ℕ) (evenPool : Bool)
    {pu pv : List ℕ} {u v : ℕ} (hu : pu.prod = u) (hv : pv.prod = v)
    (huodd : Odd u) (hvodd : Odd v) :
    (rawCommon Nat.Coprime (if evenPool then evenUniverse L else Finset.Icc 1 L) u v).card =
      coprimePrefixCount (if evenPool then L / 2 else L) ((pu ++ pv).dedup.prod) := by
  rw [coprimePrefixCount_dedup_append_prod _ hu hv]
  cases evenPool
  · exact rawCommon_coprime_Icc_card L u v
  · exact rawCommon_coprime_even_card L huodd hvodd

#print axioms coprime_dedup_append_prod_iff
#print axioms coprimePrefixCount_dedup_append_prod
#print axioms factorized_rawCommon_card
end Erdos883Verified
