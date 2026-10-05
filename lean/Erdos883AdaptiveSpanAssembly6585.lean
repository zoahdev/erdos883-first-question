import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate6585Metadata
import Erdos883AdaptiveSpan6585Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes6585 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator6585 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 288
  | 6 => 396
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator6585 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 323
  | 6 => 437
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail6585 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes6585.length) :
    SharpTailCertificate 6585 (adaptiveSpanPrimes6585.take s)
      (adaptiveSpanNumerator6585 s) (adaptiveSpanDenominator6585 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 6585 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 6585 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 6585 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 6585 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 6585 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 6585 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 6585 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 6585 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 6585 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport6585 : ∀ u ∈ oddUniverse 6585,
    ∀ v ∈ oddUniverse 6585, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid6585 : AdaptiveProfileRowsValid adaptiveRows6585 :=
  coreProfileMetadataCheck_sound adaptiveMetadata6585

theorem adaptiveSpanProfileLength6585 : adaptiveRows6585.length = halfOdds 6585 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation6585)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache6585 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes6585.length) :
    (adaptiveSpanLevel6585 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel6585 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel6585, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache6585_0 adaptiveSpanWholeCache6585_0
  · simpa only [adaptiveSpanLevel6585, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache6585_1 adaptiveSpanWholeCache6585_1
  · simpa only [adaptiveSpanLevel6585, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache6585_2 adaptiveSpanWholeCache6585_2
  · simpa only [adaptiveSpanLevel6585, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache6585_3 adaptiveSpanWholeCache6585_3
  · simpa only [adaptiveSpanLevel6585, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache6585_4 adaptiveSpanWholeCache6585_4
  · simpa only [adaptiveSpanLevel6585, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache6585_5 adaptiveSpanWholeCache6585_5
  · simpa only [adaptiveSpanLevel6585, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache6585_6 adaptiveSpanWholeCache6585_6
  · simpa only [adaptiveSpanLevel6585, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache6585_7 adaptiveSpanWholeCache6585_7
  · simpa only [adaptiveSpanLevel6585, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache6585_8 adaptiveSpanWholeCache6585_8

theorem adaptiveSpanTreeRepresents6585 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes6585.length) :
    AdaptiveSpanTreeRepresents adaptiveRows6585 (halfOdds 6585)
      (sharpDegree (5987 / 2) 7 (adaptiveSpanNumerator6585 s) (adaptiveSpanDenominator6585 s))
      (sharpDegree 5987 7 (adaptiveSpanNumerator6585 s) (adaptiveSpanDenominator6585 s))
      (adaptiveSpanLevel6585 s).1 (adaptiveSpanLevel6585 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel6585, adaptiveSpanNumerator6585, adaptiveSpanDenominator6585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3293) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid6585 adaptiveOrder6585 adaptiveSpanNumericCheck6585_0
        adaptiveSpanEven6585_0 adaptiveSpanWhole6585_0
        adaptiveSpanEvenEntries6585_0 adaptiveSpanWholeEntries6585_0
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanEvenDomain6585_0)
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanWholeDomain6585_0)
  · simpa only [adaptiveSpanLevel6585, adaptiveSpanNumerator6585, adaptiveSpanDenominator6585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3293) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid6585 adaptiveOrder6585 adaptiveSpanNumericCheck6585_1
        adaptiveSpanEven6585_1 adaptiveSpanWhole6585_1
        adaptiveSpanEvenEntries6585_1 adaptiveSpanWholeEntries6585_1
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanEvenDomain6585_1)
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanWholeDomain6585_1)
  · simpa only [adaptiveSpanLevel6585, adaptiveSpanNumerator6585, adaptiveSpanDenominator6585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3293) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid6585 adaptiveOrder6585 adaptiveSpanNumericCheck6585_2
        adaptiveSpanEven6585_2 adaptiveSpanWhole6585_2
        adaptiveSpanEvenEntries6585_2 adaptiveSpanWholeEntries6585_2
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanEvenDomain6585_2)
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanWholeDomain6585_2)
  · simpa only [adaptiveSpanLevel6585, adaptiveSpanNumerator6585, adaptiveSpanDenominator6585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3293) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid6585 adaptiveOrder6585 adaptiveSpanNumericCheck6585_3
        adaptiveSpanEven6585_3 adaptiveSpanWhole6585_3
        adaptiveSpanEvenEntries6585_3 adaptiveSpanWholeEntries6585_3
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanEvenDomain6585_3)
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanWholeDomain6585_3)
  · simpa only [adaptiveSpanLevel6585, adaptiveSpanNumerator6585, adaptiveSpanDenominator6585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3293) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid6585 adaptiveOrder6585 adaptiveSpanNumericCheck6585_4
        adaptiveSpanEven6585_4 adaptiveSpanWhole6585_4
        adaptiveSpanEvenEntries6585_4 adaptiveSpanWholeEntries6585_4
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanEvenDomain6585_4)
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanWholeDomain6585_4)
  · simpa only [adaptiveSpanLevel6585, adaptiveSpanNumerator6585, adaptiveSpanDenominator6585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3293) (by decide : 0 < 323)
        adaptiveSpanProfilesValid6585 adaptiveOrder6585 adaptiveSpanNumericCheck6585_5
        adaptiveSpanEven6585_5 adaptiveSpanWhole6585_5
        adaptiveSpanEvenEntries6585_5 adaptiveSpanWholeEntries6585_5
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanEvenDomain6585_5)
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanWholeDomain6585_5)
  · simpa only [adaptiveSpanLevel6585, adaptiveSpanNumerator6585, adaptiveSpanDenominator6585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3293) (by decide : 0 < 437)
        adaptiveSpanProfilesValid6585 adaptiveOrder6585 adaptiveSpanNumericCheck6585_6
        adaptiveSpanEven6585_6 adaptiveSpanWhole6585_6
        adaptiveSpanEvenEntries6585_6 adaptiveSpanWholeEntries6585_6
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanEvenDomain6585_6)
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanWholeDomain6585_6)
  · simpa only [adaptiveSpanLevel6585, adaptiveSpanNumerator6585, adaptiveSpanDenominator6585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3293) (by decide : 0 < 667)
        adaptiveSpanProfilesValid6585 adaptiveOrder6585 adaptiveSpanNumericCheck6585_7
        adaptiveSpanEven6585_7 adaptiveSpanWhole6585_7
        adaptiveSpanEvenEntries6585_7 adaptiveSpanWholeEntries6585_7
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanEvenDomain6585_7)
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanWholeDomain6585_7)
  · simpa only [adaptiveSpanLevel6585, adaptiveSpanNumerator6585, adaptiveSpanDenominator6585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3293) (by decide : 0 < 899)
        adaptiveSpanProfilesValid6585 adaptiveOrder6585 adaptiveSpanNumericCheck6585_8
        adaptiveSpanEven6585_8 adaptiveSpanWhole6585_8
        adaptiveSpanEvenEntries6585_8 adaptiveSpanWholeEntries6585_8
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanEvenDomain6585_8)
        (by rw [adaptiveSpanProfileLength6585]; exact adaptiveSpanWholeDomain6585_8)

/-- The complete finite histogram certificate for 5987 ≤ n ≤ 6585. -/
theorem adaptiveSpanHistogram6585 : DegreeIntervalCertificate 6585 adaptiveSpanPrimes6585
    (fun s v => sharpDegree (5987 / 2) 7 (adaptiveSpanNumerator6585 s)
      (adaptiveSpanDenominator6585 s) (totientDensity v))
    (fun s v => sharpDegree 5987 7 (adaptiveSpanNumerator6585 s)
      (adaptiveSpanDenominator6585 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows6585)
    adaptiveSpanPrimes6585
    (fun s => sharpDegree (5987 / 2) 7 (adaptiveSpanNumerator6585 s) (adaptiveSpanDenominator6585 s))
    (fun s => sharpDegree 5987 7 (adaptiveSpanNumerator6585 s) (adaptiveSpanDenominator6585 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid6585 adaptiveOrder6585 (coreOrderPermutationCheck_sound adaptivePermutation6585)
    (by rw [adaptiveSpanProfileLength6585]; decide +kernel)
    adaptiveSpanLevel6585 adaptiveSpanTreeCache6585 adaptiveSpanTreeRepresents6585
    (fun j => adaptiveSpanWitness6585.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck6585

/-- Every required odd cycle for a dense set, throughout 5987 ≤ n ≤ 6585. -/
theorem adaptiveSpanInterval6585 {n : ℕ} (hLn : 5987 ≤ n) (hnU : n ≤ 6585)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes6585
    adaptiveSpanNumerator6585 adaptiveSpanDenominator6585 adaptiveSpanSharpTail6585
    adaptiveSpanPrimeSupport6585 adaptiveSpanHistogram6585 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail6585
#print axioms adaptiveSpanPrimeSupport6585
#print axioms adaptiveSpanHistogram6585
#print axioms adaptiveSpanInterval6585
end Erdos883Verified
