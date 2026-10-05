import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2034Metadata
import Erdos883AdaptiveSpan2034Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2034 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2034 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2034 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2034 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2034.length) :
    SharpTailCertificate 2034 (adaptiveSpanPrimes2034.take s)
      (adaptiveSpanNumerator2034 s) (adaptiveSpanDenominator2034 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2034 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2034 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2034 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2034 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2034 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2034 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2034 : ∀ u ∈ oddUniverse 2034,
    ∀ v ∈ oddUniverse 2034, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2034 : AdaptiveProfileRowsValid adaptiveRows2034 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2034

theorem adaptiveSpanProfileLength2034 : adaptiveRows2034.length = halfOdds 2034 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2034)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2034 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2034.length) :
    (adaptiveSpanLevel2034 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2034 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2034, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2034_0 adaptiveSpanWholeCache2034_0
  · simpa only [adaptiveSpanLevel2034, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2034_1 adaptiveSpanWholeCache2034_1
  · simpa only [adaptiveSpanLevel2034, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2034_2 adaptiveSpanWholeCache2034_2
  · simpa only [adaptiveSpanLevel2034, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2034_3 adaptiveSpanWholeCache2034_3
  · simpa only [adaptiveSpanLevel2034, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2034_4 adaptiveSpanWholeCache2034_4
  · simpa only [adaptiveSpanLevel2034, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2034_5 adaptiveSpanWholeCache2034_5

theorem adaptiveSpanTreeRepresents2034 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2034.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2034 (halfOdds 2034)
      (sharpDegree (1985 / 2) 6 (adaptiveSpanNumerator2034 s) (adaptiveSpanDenominator2034 s))
      (sharpDegree 1985 6 (adaptiveSpanNumerator2034 s) (adaptiveSpanDenominator2034 s))
      (adaptiveSpanLevel2034 s).1 (adaptiveSpanLevel2034 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2034, adaptiveSpanNumerator2034, adaptiveSpanDenominator2034, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1017) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2034 adaptiveOrder2034 adaptiveSpanNumericCheck2034_0
        adaptiveSpanEven2034_0 adaptiveSpanWhole2034_0
        adaptiveSpanEvenEntries2034_0 adaptiveSpanWholeEntries2034_0
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanEvenDomain2034_0)
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanWholeDomain2034_0)
  · simpa only [adaptiveSpanLevel2034, adaptiveSpanNumerator2034, adaptiveSpanDenominator2034, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1017) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2034 adaptiveOrder2034 adaptiveSpanNumericCheck2034_1
        adaptiveSpanEven2034_1 adaptiveSpanWhole2034_1
        adaptiveSpanEvenEntries2034_1 adaptiveSpanWholeEntries2034_1
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanEvenDomain2034_1)
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanWholeDomain2034_1)
  · simpa only [adaptiveSpanLevel2034, adaptiveSpanNumerator2034, adaptiveSpanDenominator2034, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1017) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2034 adaptiveOrder2034 adaptiveSpanNumericCheck2034_2
        adaptiveSpanEven2034_2 adaptiveSpanWhole2034_2
        adaptiveSpanEvenEntries2034_2 adaptiveSpanWholeEntries2034_2
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanEvenDomain2034_2)
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanWholeDomain2034_2)
  · simpa only [adaptiveSpanLevel2034, adaptiveSpanNumerator2034, adaptiveSpanDenominator2034, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1017) (by decide : 0 < 143)
        adaptiveSpanProfilesValid2034 adaptiveOrder2034 adaptiveSpanNumericCheck2034_3
        adaptiveSpanEven2034_3 adaptiveSpanWhole2034_3
        adaptiveSpanEvenEntries2034_3 adaptiveSpanWholeEntries2034_3
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanEvenDomain2034_3)
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanWholeDomain2034_3)
  · simpa only [adaptiveSpanLevel2034, adaptiveSpanNumerator2034, adaptiveSpanDenominator2034, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1017) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2034 adaptiveOrder2034 adaptiveSpanNumericCheck2034_4
        adaptiveSpanEven2034_4 adaptiveSpanWhole2034_4
        adaptiveSpanEvenEntries2034_4 adaptiveSpanWholeEntries2034_4
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanEvenDomain2034_4)
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanWholeDomain2034_4)
  · simpa only [adaptiveSpanLevel2034, adaptiveSpanNumerator2034, adaptiveSpanDenominator2034, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1017) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2034 adaptiveOrder2034 adaptiveSpanNumericCheck2034_5
        adaptiveSpanEven2034_5 adaptiveSpanWhole2034_5
        adaptiveSpanEvenEntries2034_5 adaptiveSpanWholeEntries2034_5
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanEvenDomain2034_5)
        (by rw [adaptiveSpanProfileLength2034]; exact adaptiveSpanWholeDomain2034_5)

/-- The complete finite histogram certificate for 1985 ≤ n ≤ 2034. -/
theorem adaptiveSpanHistogram2034 : DegreeIntervalCertificate 2034 adaptiveSpanPrimes2034
    (fun s v => sharpDegree (1985 / 2) 6 (adaptiveSpanNumerator2034 s)
      (adaptiveSpanDenominator2034 s) (totientDensity v))
    (fun s v => sharpDegree 1985 6 (adaptiveSpanNumerator2034 s)
      (adaptiveSpanDenominator2034 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2034)
    adaptiveSpanPrimes2034
    (fun s => sharpDegree (1985 / 2) 6 (adaptiveSpanNumerator2034 s) (adaptiveSpanDenominator2034 s))
    (fun s => sharpDegree 1985 6 (adaptiveSpanNumerator2034 s) (adaptiveSpanDenominator2034 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2034 adaptiveOrder2034 (coreOrderPermutationCheck_sound adaptivePermutation2034)
    (by rw [adaptiveSpanProfileLength2034]; decide +kernel)
    adaptiveSpanLevel2034 adaptiveSpanTreeCache2034 adaptiveSpanTreeRepresents2034
    (fun j => adaptiveSpanWitness2034.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2034

/-- Every required odd cycle for a dense set, throughout 1985 ≤ n ≤ 2034. -/
theorem adaptiveSpanInterval2034 {n : ℕ} (hLn : 1985 ≤ n) (hnU : n ≤ 2034)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes2034
    adaptiveSpanNumerator2034 adaptiveSpanDenominator2034 adaptiveSpanSharpTail2034
    adaptiveSpanPrimeSupport2034 adaptiveSpanHistogram2034 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2034
#print axioms adaptiveSpanPrimeSupport2034
#print axioms adaptiveSpanHistogram2034
#print axioms adaptiveSpanInterval2034
end Erdos883Verified
