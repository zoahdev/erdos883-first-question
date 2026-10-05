import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2670Metadata
import Erdos883AdaptiveSpan2670Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2670 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2670 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2670 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2670 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2670.length) :
    SharpTailCertificate 2670 (adaptiveSpanPrimes2670.take s)
      (adaptiveSpanNumerator2670 s) (adaptiveSpanDenominator2670 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2670 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2670 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2670 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2670 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2670 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2670 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2670 : ∀ u ∈ oddUniverse 2670,
    ∀ v ∈ oddUniverse 2670, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2670 : AdaptiveProfileRowsValid adaptiveRows2670 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2670

theorem adaptiveSpanProfileLength2670 : adaptiveRows2670.length = halfOdds 2670 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2670)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2670 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2670.length) :
    (adaptiveSpanLevel2670 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2670 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2670, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2670_0 adaptiveSpanWholeCache2670_0
  · simpa only [adaptiveSpanLevel2670, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2670_1 adaptiveSpanWholeCache2670_1
  · simpa only [adaptiveSpanLevel2670, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2670_2 adaptiveSpanWholeCache2670_2
  · simpa only [adaptiveSpanLevel2670, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2670_3 adaptiveSpanWholeCache2670_3
  · simpa only [adaptiveSpanLevel2670, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2670_4 adaptiveSpanWholeCache2670_4
  · simpa only [adaptiveSpanLevel2670, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2670_5 adaptiveSpanWholeCache2670_5

theorem adaptiveSpanTreeRepresents2670 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2670.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2670 (halfOdds 2670)
      (sharpDegree (2605 / 2) 7 (adaptiveSpanNumerator2670 s) (adaptiveSpanDenominator2670 s))
      (sharpDegree 2605 7 (adaptiveSpanNumerator2670 s) (adaptiveSpanDenominator2670 s))
      (adaptiveSpanLevel2670 s).1 (adaptiveSpanLevel2670 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2670, adaptiveSpanNumerator2670, adaptiveSpanDenominator2670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1335) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2670 adaptiveOrder2670 adaptiveSpanNumericCheck2670_0
        adaptiveSpanEven2670_0 adaptiveSpanWhole2670_0
        adaptiveSpanEvenEntries2670_0 adaptiveSpanWholeEntries2670_0
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanEvenDomain2670_0)
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanWholeDomain2670_0)
  · simpa only [adaptiveSpanLevel2670, adaptiveSpanNumerator2670, adaptiveSpanDenominator2670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1335) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2670 adaptiveOrder2670 adaptiveSpanNumericCheck2670_1
        adaptiveSpanEven2670_1 adaptiveSpanWhole2670_1
        adaptiveSpanEvenEntries2670_1 adaptiveSpanWholeEntries2670_1
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanEvenDomain2670_1)
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanWholeDomain2670_1)
  · simpa only [adaptiveSpanLevel2670, adaptiveSpanNumerator2670, adaptiveSpanDenominator2670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1335) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2670 adaptiveOrder2670 adaptiveSpanNumericCheck2670_2
        adaptiveSpanEven2670_2 adaptiveSpanWhole2670_2
        adaptiveSpanEvenEntries2670_2 adaptiveSpanWholeEntries2670_2
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanEvenDomain2670_2)
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanWholeDomain2670_2)
  · simpa only [adaptiveSpanLevel2670, adaptiveSpanNumerator2670, adaptiveSpanDenominator2670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1335) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid2670 adaptiveOrder2670 adaptiveSpanNumericCheck2670_3
        adaptiveSpanEven2670_3 adaptiveSpanWhole2670_3
        adaptiveSpanEvenEntries2670_3 adaptiveSpanWholeEntries2670_3
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanEvenDomain2670_3)
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanWholeDomain2670_3)
  · simpa only [adaptiveSpanLevel2670, adaptiveSpanNumerator2670, adaptiveSpanDenominator2670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1335) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2670 adaptiveOrder2670 adaptiveSpanNumericCheck2670_4
        adaptiveSpanEven2670_4 adaptiveSpanWhole2670_4
        adaptiveSpanEvenEntries2670_4 adaptiveSpanWholeEntries2670_4
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanEvenDomain2670_4)
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanWholeDomain2670_4)
  · simpa only [adaptiveSpanLevel2670, adaptiveSpanNumerator2670, adaptiveSpanDenominator2670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1335) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2670 adaptiveOrder2670 adaptiveSpanNumericCheck2670_5
        adaptiveSpanEven2670_5 adaptiveSpanWhole2670_5
        adaptiveSpanEvenEntries2670_5 adaptiveSpanWholeEntries2670_5
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanEvenDomain2670_5)
        (by rw [adaptiveSpanProfileLength2670]; exact adaptiveSpanWholeDomain2670_5)

/-- The complete finite histogram certificate for 2605 ≤ n ≤ 2670. -/
theorem adaptiveSpanHistogram2670 : DegreeIntervalCertificate 2670 adaptiveSpanPrimes2670
    (fun s v => sharpDegree (2605 / 2) 7 (adaptiveSpanNumerator2670 s)
      (adaptiveSpanDenominator2670 s) (totientDensity v))
    (fun s v => sharpDegree 2605 7 (adaptiveSpanNumerator2670 s)
      (adaptiveSpanDenominator2670 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2670)
    adaptiveSpanPrimes2670
    (fun s => sharpDegree (2605 / 2) 7 (adaptiveSpanNumerator2670 s) (adaptiveSpanDenominator2670 s))
    (fun s => sharpDegree 2605 7 (adaptiveSpanNumerator2670 s) (adaptiveSpanDenominator2670 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2670 adaptiveOrder2670 (coreOrderPermutationCheck_sound adaptivePermutation2670)
    (by rw [adaptiveSpanProfileLength2670]; decide +kernel)
    adaptiveSpanLevel2670 adaptiveSpanTreeCache2670 adaptiveSpanTreeRepresents2670
    (fun j => adaptiveSpanWitness2670.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2670

/-- Every required odd cycle for a dense set, throughout 2605 ≤ n ≤ 2670. -/
theorem adaptiveSpanInterval2670 {n : ℕ} (hLn : 2605 ≤ n) (hnU : n ≤ 2670)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes2670
    adaptiveSpanNumerator2670 adaptiveSpanDenominator2670 adaptiveSpanSharpTail2670
    adaptiveSpanPrimeSupport2670 adaptiveSpanHistogram2670 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2670
#print axioms adaptiveSpanPrimeSupport2670
#print axioms adaptiveSpanHistogram2670
#print axioms adaptiveSpanInterval2670
end Erdos883Verified
