import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate14124Metadata
import Erdos883AdaptiveSpan14124Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate14124PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes14124 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator14124 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator14124 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail14124 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes14124.length) :
    SharpTailCertificate 14124 (adaptiveSpanPrimes14124.take s)
      (adaptiveSpanNumerator14124 s) (adaptiveSpanDenominator14124 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 14124 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 14124 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 14124 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 14124 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 14124 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 14124 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 14124 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 14124 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 14124 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport14124 : ∀ u ∈ oddUniverse 14124,
    ∀ v ∈ oddUniverse 14124, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid14124 : AdaptiveProfileRowsValid adaptiveRows14124 :=
  coreProfileMetadataCheck_sound adaptiveMetadata14124

theorem adaptiveSpanProfileLength14124 : adaptiveRows14124.length = halfOdds 14124 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics14124
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache14124 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes14124.length) :
    (adaptiveSpanLevel14124 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel14124 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel14124, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache14124_0 adaptiveSpanWholeCache14124_0
  · simpa only [adaptiveSpanLevel14124, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache14124_1 adaptiveSpanWholeCache14124_1
  · simpa only [adaptiveSpanLevel14124, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache14124_2 adaptiveSpanWholeCache14124_2
  · simpa only [adaptiveSpanLevel14124, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache14124_3 adaptiveSpanWholeCache14124_3
  · simpa only [adaptiveSpanLevel14124, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache14124_4 adaptiveSpanWholeCache14124_4
  · simpa only [adaptiveSpanLevel14124, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache14124_5 adaptiveSpanWholeCache14124_5
  · simpa only [adaptiveSpanLevel14124, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache14124_6 adaptiveSpanWholeCache14124_6
  · simpa only [adaptiveSpanLevel14124, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache14124_7 adaptiveSpanWholeCache14124_7
  · simpa only [adaptiveSpanLevel14124, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache14124_8 adaptiveSpanWholeCache14124_8

theorem adaptiveSpanTreeRepresents14124 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes14124.length) :
    AdaptiveSpanTreeRepresents adaptiveRows14124 (halfOdds 14124)
      (sharpDegree (12840 / 2) 8 (adaptiveSpanNumerator14124 s) (adaptiveSpanDenominator14124 s))
      (sharpDegree 12840 8 (adaptiveSpanNumerator14124 s) (adaptiveSpanDenominator14124 s))
      (adaptiveSpanLevel14124 s).1 (adaptiveSpanLevel14124 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel14124, adaptiveSpanNumerator14124, adaptiveSpanDenominator14124, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7062) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid14124 adaptiveOrder14124 adaptiveSpanNumericCheck14124_0
        adaptiveSpanEven14124_0 adaptiveSpanWhole14124_0
        adaptiveSpanEvenEntries14124_0 adaptiveSpanWholeEntries14124_0
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanEvenDomain14124_0)
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanWholeDomain14124_0)
  · simpa only [adaptiveSpanLevel14124, adaptiveSpanNumerator14124, adaptiveSpanDenominator14124, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7062) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid14124 adaptiveOrder14124 adaptiveSpanNumericCheck14124_1
        adaptiveSpanEven14124_1 adaptiveSpanWhole14124_1
        adaptiveSpanEvenEntries14124_1 adaptiveSpanWholeEntries14124_1
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanEvenDomain14124_1)
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanWholeDomain14124_1)
  · simpa only [adaptiveSpanLevel14124, adaptiveSpanNumerator14124, adaptiveSpanDenominator14124, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7062) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid14124 adaptiveOrder14124 adaptiveSpanNumericCheck14124_2
        adaptiveSpanEven14124_2 adaptiveSpanWhole14124_2
        adaptiveSpanEvenEntries14124_2 adaptiveSpanWholeEntries14124_2
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanEvenDomain14124_2)
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanWholeDomain14124_2)
  · simpa only [adaptiveSpanLevel14124, adaptiveSpanNumerator14124, adaptiveSpanDenominator14124, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7062) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid14124 adaptiveOrder14124 adaptiveSpanNumericCheck14124_3
        adaptiveSpanEven14124_3 adaptiveSpanWhole14124_3
        adaptiveSpanEvenEntries14124_3 adaptiveSpanWholeEntries14124_3
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanEvenDomain14124_3)
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanWholeDomain14124_3)
  · simpa only [adaptiveSpanLevel14124, adaptiveSpanNumerator14124, adaptiveSpanDenominator14124, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7062) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid14124 adaptiveOrder14124 adaptiveSpanNumericCheck14124_4
        adaptiveSpanEven14124_4 adaptiveSpanWhole14124_4
        adaptiveSpanEvenEntries14124_4 adaptiveSpanWholeEntries14124_4
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanEvenDomain14124_4)
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanWholeDomain14124_4)
  · simpa only [adaptiveSpanLevel14124, adaptiveSpanNumerator14124, adaptiveSpanDenominator14124, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7062) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid14124 adaptiveOrder14124 adaptiveSpanNumericCheck14124_5
        adaptiveSpanEven14124_5 adaptiveSpanWhole14124_5
        adaptiveSpanEvenEntries14124_5 adaptiveSpanWholeEntries14124_5
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanEvenDomain14124_5)
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanWholeDomain14124_5)
  · simpa only [adaptiveSpanLevel14124, adaptiveSpanNumerator14124, adaptiveSpanDenominator14124, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7062) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid14124 adaptiveOrder14124 adaptiveSpanNumericCheck14124_6
        adaptiveSpanEven14124_6 adaptiveSpanWhole14124_6
        adaptiveSpanEvenEntries14124_6 adaptiveSpanWholeEntries14124_6
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanEvenDomain14124_6)
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanWholeDomain14124_6)
  · simpa only [adaptiveSpanLevel14124, adaptiveSpanNumerator14124, adaptiveSpanDenominator14124, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7062) (by decide : 0 < 667)
        adaptiveSpanProfilesValid14124 adaptiveOrder14124 adaptiveSpanNumericCheck14124_7
        adaptiveSpanEven14124_7 adaptiveSpanWhole14124_7
        adaptiveSpanEvenEntries14124_7 adaptiveSpanWholeEntries14124_7
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanEvenDomain14124_7)
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanWholeDomain14124_7)
  · simpa only [adaptiveSpanLevel14124, adaptiveSpanNumerator14124, adaptiveSpanDenominator14124, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7062) (by decide : 0 < 899)
        adaptiveSpanProfilesValid14124 adaptiveOrder14124 adaptiveSpanNumericCheck14124_8
        adaptiveSpanEven14124_8 adaptiveSpanWhole14124_8
        adaptiveSpanEvenEntries14124_8 adaptiveSpanWholeEntries14124_8
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanEvenDomain14124_8)
        (by rw [adaptiveSpanProfileLength14124]; exact adaptiveSpanWholeDomain14124_8)

/-- The complete finite histogram certificate for 12840 ≤ n ≤ 14124. -/
theorem adaptiveSpanHistogram14124 : DegreeIntervalCertificate 14124 adaptiveSpanPrimes14124
    (fun s v => sharpDegree (12840 / 2) 8 (adaptiveSpanNumerator14124 s)
      (adaptiveSpanDenominator14124 s) (totientDensity v))
    (fun s v => sharpDegree 12840 8 (adaptiveSpanNumerator14124 s)
      (adaptiveSpanDenominator14124 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows14124)
    adaptiveSpanPrimes14124
    (fun s => sharpDegree (12840 / 2) 8 (adaptiveSpanNumerator14124 s) (adaptiveSpanDenominator14124 s))
    (fun s => sharpDegree 12840 8 (adaptiveSpanNumerator14124 s) (adaptiveSpanDenominator14124 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid14124 adaptiveOrder14124 adaptivePermutationSemantics14124
    (by rw [adaptiveSpanProfileLength14124]; decide +kernel)
    adaptiveSpanLevel14124 adaptiveSpanTreeCache14124 adaptiveSpanTreeRepresents14124
    (fun j => adaptiveSpanWitness14124.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength14124
  · exact adaptiveSpanWitnessCheck14124

/-- Every required odd cycle for a dense set, throughout 12840 ≤ n ≤ 14124. -/
theorem adaptiveSpanInterval14124 {n : ℕ} (hLn : 12840 ≤ n) (hnU : n ≤ 14124)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes14124
    adaptiveSpanNumerator14124 adaptiveSpanDenominator14124 adaptiveSpanSharpTail14124
    adaptiveSpanPrimeSupport14124 adaptiveSpanHistogram14124 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail14124
#print axioms adaptiveSpanPrimeSupport14124
#print axioms adaptiveSpanHistogram14124
#print axioms adaptiveSpanInterval14124
end Erdos883Verified
