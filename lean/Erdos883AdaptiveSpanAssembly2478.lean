import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2478Metadata
import Erdos883AdaptiveSpan2478Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2478 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2478 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2478 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2478 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2478.length) :
    SharpTailCertificate 2478 (adaptiveSpanPrimes2478.take s)
      (adaptiveSpanNumerator2478 s) (adaptiveSpanDenominator2478 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2478 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2478 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2478 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2478 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2478 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2478 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2478 : ∀ u ∈ oddUniverse 2478,
    ∀ v ∈ oddUniverse 2478, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2478 : AdaptiveProfileRowsValid adaptiveRows2478 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2478

theorem adaptiveSpanProfileLength2478 : adaptiveRows2478.length = halfOdds 2478 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2478)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2478 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2478.length) :
    (adaptiveSpanLevel2478 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2478 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2478, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2478_0 adaptiveSpanWholeCache2478_0
  · simpa only [adaptiveSpanLevel2478, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2478_1 adaptiveSpanWholeCache2478_1
  · simpa only [adaptiveSpanLevel2478, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2478_2 adaptiveSpanWholeCache2478_2
  · simpa only [adaptiveSpanLevel2478, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2478_3 adaptiveSpanWholeCache2478_3
  · simpa only [adaptiveSpanLevel2478, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2478_4 adaptiveSpanWholeCache2478_4
  · simpa only [adaptiveSpanLevel2478, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2478_5 adaptiveSpanWholeCache2478_5

theorem adaptiveSpanTreeRepresents2478 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2478.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2478 (halfOdds 2478)
      (sharpDegree (2418 / 2) 7 (adaptiveSpanNumerator2478 s) (adaptiveSpanDenominator2478 s))
      (sharpDegree 2418 7 (adaptiveSpanNumerator2478 s) (adaptiveSpanDenominator2478 s))
      (adaptiveSpanLevel2478 s).1 (adaptiveSpanLevel2478 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2478, adaptiveSpanNumerator2478, adaptiveSpanDenominator2478, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1239) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2478 adaptiveOrder2478 adaptiveSpanNumericCheck2478_0
        adaptiveSpanEven2478_0 adaptiveSpanWhole2478_0
        adaptiveSpanEvenEntries2478_0 adaptiveSpanWholeEntries2478_0
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanEvenDomain2478_0)
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanWholeDomain2478_0)
  · simpa only [adaptiveSpanLevel2478, adaptiveSpanNumerator2478, adaptiveSpanDenominator2478, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1239) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2478 adaptiveOrder2478 adaptiveSpanNumericCheck2478_1
        adaptiveSpanEven2478_1 adaptiveSpanWhole2478_1
        adaptiveSpanEvenEntries2478_1 adaptiveSpanWholeEntries2478_1
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanEvenDomain2478_1)
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanWholeDomain2478_1)
  · simpa only [adaptiveSpanLevel2478, adaptiveSpanNumerator2478, adaptiveSpanDenominator2478, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1239) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2478 adaptiveOrder2478 adaptiveSpanNumericCheck2478_2
        adaptiveSpanEven2478_2 adaptiveSpanWhole2478_2
        adaptiveSpanEvenEntries2478_2 adaptiveSpanWholeEntries2478_2
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanEvenDomain2478_2)
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanWholeDomain2478_2)
  · simpa only [adaptiveSpanLevel2478, adaptiveSpanNumerator2478, adaptiveSpanDenominator2478, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1239) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid2478 adaptiveOrder2478 adaptiveSpanNumericCheck2478_3
        adaptiveSpanEven2478_3 adaptiveSpanWhole2478_3
        adaptiveSpanEvenEntries2478_3 adaptiveSpanWholeEntries2478_3
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanEvenDomain2478_3)
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanWholeDomain2478_3)
  · simpa only [adaptiveSpanLevel2478, adaptiveSpanNumerator2478, adaptiveSpanDenominator2478, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1239) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2478 adaptiveOrder2478 adaptiveSpanNumericCheck2478_4
        adaptiveSpanEven2478_4 adaptiveSpanWhole2478_4
        adaptiveSpanEvenEntries2478_4 adaptiveSpanWholeEntries2478_4
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanEvenDomain2478_4)
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanWholeDomain2478_4)
  · simpa only [adaptiveSpanLevel2478, adaptiveSpanNumerator2478, adaptiveSpanDenominator2478, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1239) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2478 adaptiveOrder2478 adaptiveSpanNumericCheck2478_5
        adaptiveSpanEven2478_5 adaptiveSpanWhole2478_5
        adaptiveSpanEvenEntries2478_5 adaptiveSpanWholeEntries2478_5
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanEvenDomain2478_5)
        (by rw [adaptiveSpanProfileLength2478]; exact adaptiveSpanWholeDomain2478_5)

/-- The complete finite histogram certificate for 2418 ≤ n ≤ 2478. -/
theorem adaptiveSpanHistogram2478 : DegreeIntervalCertificate 2478 adaptiveSpanPrimes2478
    (fun s v => sharpDegree (2418 / 2) 7 (adaptiveSpanNumerator2478 s)
      (adaptiveSpanDenominator2478 s) (totientDensity v))
    (fun s v => sharpDegree 2418 7 (adaptiveSpanNumerator2478 s)
      (adaptiveSpanDenominator2478 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2478)
    adaptiveSpanPrimes2478
    (fun s => sharpDegree (2418 / 2) 7 (adaptiveSpanNumerator2478 s) (adaptiveSpanDenominator2478 s))
    (fun s => sharpDegree 2418 7 (adaptiveSpanNumerator2478 s) (adaptiveSpanDenominator2478 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2478 adaptiveOrder2478 (coreOrderPermutationCheck_sound adaptivePermutation2478)
    (by rw [adaptiveSpanProfileLength2478]; decide +kernel)
    adaptiveSpanLevel2478 adaptiveSpanTreeCache2478 adaptiveSpanTreeRepresents2478
    (fun j => adaptiveSpanWitness2478.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2478

/-- Every required odd cycle for a dense set, throughout 2418 ≤ n ≤ 2478. -/
theorem adaptiveSpanInterval2478 {n : ℕ} (hLn : 2418 ≤ n) (hnU : n ≤ 2478)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes2478
    adaptiveSpanNumerator2478 adaptiveSpanDenominator2478 adaptiveSpanSharpTail2478
    adaptiveSpanPrimeSupport2478 adaptiveSpanHistogram2478 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2478
#print axioms adaptiveSpanPrimeSupport2478
#print axioms adaptiveSpanHistogram2478
#print axioms adaptiveSpanInterval2478
end Erdos883Verified
