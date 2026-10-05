import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2540Metadata
import Erdos883AdaptiveSpan2540Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2540 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2540 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2540 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2540 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2540.length) :
    SharpTailCertificate 2540 (adaptiveSpanPrimes2540.take s)
      (adaptiveSpanNumerator2540 s) (adaptiveSpanDenominator2540 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2540 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2540 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2540 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2540 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2540 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2540 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2540 : ∀ u ∈ oddUniverse 2540,
    ∀ v ∈ oddUniverse 2540, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2540 : AdaptiveProfileRowsValid adaptiveRows2540 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2540

theorem adaptiveSpanProfileLength2540 : adaptiveRows2540.length = halfOdds 2540 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2540)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2540 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2540.length) :
    (adaptiveSpanLevel2540 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2540 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2540, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2540_0 adaptiveSpanWholeCache2540_0
  · simpa only [adaptiveSpanLevel2540, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2540_1 adaptiveSpanWholeCache2540_1
  · simpa only [adaptiveSpanLevel2540, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2540_2 adaptiveSpanWholeCache2540_2
  · simpa only [adaptiveSpanLevel2540, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2540_3 adaptiveSpanWholeCache2540_3
  · simpa only [adaptiveSpanLevel2540, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2540_4 adaptiveSpanWholeCache2540_4
  · simpa only [adaptiveSpanLevel2540, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2540_5 adaptiveSpanWholeCache2540_5

theorem adaptiveSpanTreeRepresents2540 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2540.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2540 (halfOdds 2540)
      (sharpDegree (2479 / 2) 7 (adaptiveSpanNumerator2540 s) (adaptiveSpanDenominator2540 s))
      (sharpDegree 2479 7 (adaptiveSpanNumerator2540 s) (adaptiveSpanDenominator2540 s))
      (adaptiveSpanLevel2540 s).1 (adaptiveSpanLevel2540 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2540, adaptiveSpanNumerator2540, adaptiveSpanDenominator2540, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1270) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2540 adaptiveOrder2540 adaptiveSpanNumericCheck2540_0
        adaptiveSpanEven2540_0 adaptiveSpanWhole2540_0
        adaptiveSpanEvenEntries2540_0 adaptiveSpanWholeEntries2540_0
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanEvenDomain2540_0)
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanWholeDomain2540_0)
  · simpa only [adaptiveSpanLevel2540, adaptiveSpanNumerator2540, adaptiveSpanDenominator2540, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1270) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2540 adaptiveOrder2540 adaptiveSpanNumericCheck2540_1
        adaptiveSpanEven2540_1 adaptiveSpanWhole2540_1
        adaptiveSpanEvenEntries2540_1 adaptiveSpanWholeEntries2540_1
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanEvenDomain2540_1)
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanWholeDomain2540_1)
  · simpa only [adaptiveSpanLevel2540, adaptiveSpanNumerator2540, adaptiveSpanDenominator2540, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1270) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2540 adaptiveOrder2540 adaptiveSpanNumericCheck2540_2
        adaptiveSpanEven2540_2 adaptiveSpanWhole2540_2
        adaptiveSpanEvenEntries2540_2 adaptiveSpanWholeEntries2540_2
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanEvenDomain2540_2)
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanWholeDomain2540_2)
  · simpa only [adaptiveSpanLevel2540, adaptiveSpanNumerator2540, adaptiveSpanDenominator2540, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1270) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid2540 adaptiveOrder2540 adaptiveSpanNumericCheck2540_3
        adaptiveSpanEven2540_3 adaptiveSpanWhole2540_3
        adaptiveSpanEvenEntries2540_3 adaptiveSpanWholeEntries2540_3
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanEvenDomain2540_3)
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanWholeDomain2540_3)
  · simpa only [adaptiveSpanLevel2540, adaptiveSpanNumerator2540, adaptiveSpanDenominator2540, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1270) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2540 adaptiveOrder2540 adaptiveSpanNumericCheck2540_4
        adaptiveSpanEven2540_4 adaptiveSpanWhole2540_4
        adaptiveSpanEvenEntries2540_4 adaptiveSpanWholeEntries2540_4
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanEvenDomain2540_4)
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanWholeDomain2540_4)
  · simpa only [adaptiveSpanLevel2540, adaptiveSpanNumerator2540, adaptiveSpanDenominator2540, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1270) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2540 adaptiveOrder2540 adaptiveSpanNumericCheck2540_5
        adaptiveSpanEven2540_5 adaptiveSpanWhole2540_5
        adaptiveSpanEvenEntries2540_5 adaptiveSpanWholeEntries2540_5
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanEvenDomain2540_5)
        (by rw [adaptiveSpanProfileLength2540]; exact adaptiveSpanWholeDomain2540_5)

/-- The complete finite histogram certificate for 2479 ≤ n ≤ 2540. -/
theorem adaptiveSpanHistogram2540 : DegreeIntervalCertificate 2540 adaptiveSpanPrimes2540
    (fun s v => sharpDegree (2479 / 2) 7 (adaptiveSpanNumerator2540 s)
      (adaptiveSpanDenominator2540 s) (totientDensity v))
    (fun s v => sharpDegree 2479 7 (adaptiveSpanNumerator2540 s)
      (adaptiveSpanDenominator2540 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2540)
    adaptiveSpanPrimes2540
    (fun s => sharpDegree (2479 / 2) 7 (adaptiveSpanNumerator2540 s) (adaptiveSpanDenominator2540 s))
    (fun s => sharpDegree 2479 7 (adaptiveSpanNumerator2540 s) (adaptiveSpanDenominator2540 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2540 adaptiveOrder2540 (coreOrderPermutationCheck_sound adaptivePermutation2540)
    (by rw [adaptiveSpanProfileLength2540]; decide +kernel)
    adaptiveSpanLevel2540 adaptiveSpanTreeCache2540 adaptiveSpanTreeRepresents2540
    (fun j => adaptiveSpanWitness2540.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2540

/-- Every required odd cycle for a dense set, throughout 2479 ≤ n ≤ 2540. -/
theorem adaptiveSpanInterval2540 {n : ℕ} (hLn : 2479 ≤ n) (hnU : n ≤ 2540)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes2540
    adaptiveSpanNumerator2540 adaptiveSpanDenominator2540 adaptiveSpanSharpTail2540
    adaptiveSpanPrimeSupport2540 adaptiveSpanHistogram2540 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2540
#print axioms adaptiveSpanPrimeSupport2540
#print axioms adaptiveSpanHistogram2540
#print axioms adaptiveSpanInterval2540
end Erdos883Verified
