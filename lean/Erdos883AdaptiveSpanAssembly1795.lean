import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1795Metadata
import Erdos883AdaptiveSpan1795Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1795 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1795 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1795 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1795 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1795.length) :
    SharpTailCertificate 1795 (adaptiveSpanPrimes1795.take s)
      (adaptiveSpanNumerator1795 s) (adaptiveSpanDenominator1795 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1795 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1795 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1795 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1795 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1795 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1795 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1795 : ∀ u ∈ oddUniverse 1795,
    ∀ v ∈ oddUniverse 1795, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1795 : AdaptiveProfileRowsValid adaptiveRows1795 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1795

theorem adaptiveSpanProfileLength1795 : adaptiveRows1795.length = halfOdds 1795 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1795)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1795 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1795.length) :
    (adaptiveSpanLevel1795 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1795 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1795, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1795_0 adaptiveSpanWholeCache1795_0
  · simpa only [adaptiveSpanLevel1795, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1795_1 adaptiveSpanWholeCache1795_1
  · simpa only [adaptiveSpanLevel1795, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1795_2 adaptiveSpanWholeCache1795_2
  · simpa only [adaptiveSpanLevel1795, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1795_3 adaptiveSpanWholeCache1795_3
  · simpa only [adaptiveSpanLevel1795, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1795_4 adaptiveSpanWholeCache1795_4
  · simpa only [adaptiveSpanLevel1795, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1795_5 adaptiveSpanWholeCache1795_5

theorem adaptiveSpanTreeRepresents1795 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1795.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1795 (halfOdds 1795)
      (sharpDegree (1752 / 2) 6 (adaptiveSpanNumerator1795 s) (adaptiveSpanDenominator1795 s))
      (sharpDegree 1752 6 (adaptiveSpanNumerator1795 s) (adaptiveSpanDenominator1795 s))
      (adaptiveSpanLevel1795 s).1 (adaptiveSpanLevel1795 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1795, adaptiveSpanNumerator1795, adaptiveSpanDenominator1795, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 898) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1795 adaptiveOrder1795 adaptiveSpanNumericCheck1795_0
        adaptiveSpanEven1795_0 adaptiveSpanWhole1795_0
        adaptiveSpanEvenEntries1795_0 adaptiveSpanWholeEntries1795_0
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanEvenDomain1795_0)
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanWholeDomain1795_0)
  · simpa only [adaptiveSpanLevel1795, adaptiveSpanNumerator1795, adaptiveSpanDenominator1795, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 898) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1795 adaptiveOrder1795 adaptiveSpanNumericCheck1795_1
        adaptiveSpanEven1795_1 adaptiveSpanWhole1795_1
        adaptiveSpanEvenEntries1795_1 adaptiveSpanWholeEntries1795_1
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanEvenDomain1795_1)
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanWholeDomain1795_1)
  · simpa only [adaptiveSpanLevel1795, adaptiveSpanNumerator1795, adaptiveSpanDenominator1795, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 898) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1795 adaptiveOrder1795 adaptiveSpanNumericCheck1795_2
        adaptiveSpanEven1795_2 adaptiveSpanWhole1795_2
        adaptiveSpanEvenEntries1795_2 adaptiveSpanWholeEntries1795_2
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanEvenDomain1795_2)
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanWholeDomain1795_2)
  · simpa only [adaptiveSpanLevel1795, adaptiveSpanNumerator1795, adaptiveSpanDenominator1795, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 898) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1795 adaptiveOrder1795 adaptiveSpanNumericCheck1795_3
        adaptiveSpanEven1795_3 adaptiveSpanWhole1795_3
        adaptiveSpanEvenEntries1795_3 adaptiveSpanWholeEntries1795_3
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanEvenDomain1795_3)
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanWholeDomain1795_3)
  · simpa only [adaptiveSpanLevel1795, adaptiveSpanNumerator1795, adaptiveSpanDenominator1795, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 898) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1795 adaptiveOrder1795 adaptiveSpanNumericCheck1795_4
        adaptiveSpanEven1795_4 adaptiveSpanWhole1795_4
        adaptiveSpanEvenEntries1795_4 adaptiveSpanWholeEntries1795_4
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanEvenDomain1795_4)
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanWholeDomain1795_4)
  · simpa only [adaptiveSpanLevel1795, adaptiveSpanNumerator1795, adaptiveSpanDenominator1795, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 898) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1795 adaptiveOrder1795 adaptiveSpanNumericCheck1795_5
        adaptiveSpanEven1795_5 adaptiveSpanWhole1795_5
        adaptiveSpanEvenEntries1795_5 adaptiveSpanWholeEntries1795_5
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanEvenDomain1795_5)
        (by rw [adaptiveSpanProfileLength1795]; exact adaptiveSpanWholeDomain1795_5)

/-- The complete finite histogram certificate for 1752 ≤ n ≤ 1795. -/
theorem adaptiveSpanHistogram1795 : DegreeIntervalCertificate 1795 adaptiveSpanPrimes1795
    (fun s v => sharpDegree (1752 / 2) 6 (adaptiveSpanNumerator1795 s)
      (adaptiveSpanDenominator1795 s) (totientDensity v))
    (fun s v => sharpDegree 1752 6 (adaptiveSpanNumerator1795 s)
      (adaptiveSpanDenominator1795 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1795)
    adaptiveSpanPrimes1795
    (fun s => sharpDegree (1752 / 2) 6 (adaptiveSpanNumerator1795 s) (adaptiveSpanDenominator1795 s))
    (fun s => sharpDegree 1752 6 (adaptiveSpanNumerator1795 s) (adaptiveSpanDenominator1795 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1795 adaptiveOrder1795 (coreOrderPermutationCheck_sound adaptivePermutation1795)
    (by rw [adaptiveSpanProfileLength1795]; decide +kernel)
    adaptiveSpanLevel1795 adaptiveSpanTreeCache1795 adaptiveSpanTreeRepresents1795
    (fun j => adaptiveSpanWitness1795.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1795

/-- Every required odd cycle for a dense set, throughout 1752 ≤ n ≤ 1795. -/
theorem adaptiveSpanInterval1795 {n : ℕ} (hLn : 1752 ≤ n) (hnU : n ≤ 1795)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1795
    adaptiveSpanNumerator1795 adaptiveSpanDenominator1795 adaptiveSpanSharpTail1795
    adaptiveSpanPrimeSupport1795 adaptiveSpanHistogram1795 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1795
#print axioms adaptiveSpanPrimeSupport1795
#print axioms adaptiveSpanHistogram1795
#print axioms adaptiveSpanInterval1795
end Erdos883Verified
