import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2874Metadata
import Erdos883AdaptiveSpan2874Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2874 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator2874 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator2874 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail2874 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2874.length) :
    SharpTailCertificate 2874 (adaptiveSpanPrimes2874.take s)
      (adaptiveSpanNumerator2874 s) (adaptiveSpanDenominator2874 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2874 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2874 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2874 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2874 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2874 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2874 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2874 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2874 : ∀ u ∈ oddUniverse 2874,
    ∀ v ∈ oddUniverse 2874, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2874 : AdaptiveProfileRowsValid adaptiveRows2874 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2874

theorem adaptiveSpanProfileLength2874 : adaptiveRows2874.length = halfOdds 2874 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2874)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2874 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2874.length) :
    (adaptiveSpanLevel2874 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2874 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2874, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2874_0 adaptiveSpanWholeCache2874_0
  · simpa only [adaptiveSpanLevel2874, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2874_1 adaptiveSpanWholeCache2874_1
  · simpa only [adaptiveSpanLevel2874, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2874_2 adaptiveSpanWholeCache2874_2
  · simpa only [adaptiveSpanLevel2874, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2874_3 adaptiveSpanWholeCache2874_3
  · simpa only [adaptiveSpanLevel2874, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2874_4 adaptiveSpanWholeCache2874_4
  · simpa only [adaptiveSpanLevel2874, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2874_5 adaptiveSpanWholeCache2874_5
  · simpa only [adaptiveSpanLevel2874, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2874_6 adaptiveSpanWholeCache2874_6

theorem adaptiveSpanTreeRepresents2874 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2874.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2874 (halfOdds 2874)
      (sharpDegree (2738 / 2) 7 (adaptiveSpanNumerator2874 s) (adaptiveSpanDenominator2874 s))
      (sharpDegree 2738 7 (adaptiveSpanNumerator2874 s) (adaptiveSpanDenominator2874 s))
      (adaptiveSpanLevel2874 s).1 (adaptiveSpanLevel2874 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2874, adaptiveSpanNumerator2874, adaptiveSpanDenominator2874, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1437) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2874 adaptiveOrder2874 adaptiveSpanNumericCheck2874_0
        adaptiveSpanEven2874_0 adaptiveSpanWhole2874_0
        adaptiveSpanEvenEntries2874_0 adaptiveSpanWholeEntries2874_0
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanEvenDomain2874_0)
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanWholeDomain2874_0)
  · simpa only [adaptiveSpanLevel2874, adaptiveSpanNumerator2874, adaptiveSpanDenominator2874, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1437) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2874 adaptiveOrder2874 adaptiveSpanNumericCheck2874_1
        adaptiveSpanEven2874_1 adaptiveSpanWhole2874_1
        adaptiveSpanEvenEntries2874_1 adaptiveSpanWholeEntries2874_1
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanEvenDomain2874_1)
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanWholeDomain2874_1)
  · simpa only [adaptiveSpanLevel2874, adaptiveSpanNumerator2874, adaptiveSpanDenominator2874, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1437) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2874 adaptiveOrder2874 adaptiveSpanNumericCheck2874_2
        adaptiveSpanEven2874_2 adaptiveSpanWhole2874_2
        adaptiveSpanEvenEntries2874_2 adaptiveSpanWholeEntries2874_2
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanEvenDomain2874_2)
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanWholeDomain2874_2)
  · simpa only [adaptiveSpanLevel2874, adaptiveSpanNumerator2874, adaptiveSpanDenominator2874, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1437) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid2874 adaptiveOrder2874 adaptiveSpanNumericCheck2874_3
        adaptiveSpanEven2874_3 adaptiveSpanWhole2874_3
        adaptiveSpanEvenEntries2874_3 adaptiveSpanWholeEntries2874_3
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanEvenDomain2874_3)
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanWholeDomain2874_3)
  · simpa only [adaptiveSpanLevel2874, adaptiveSpanNumerator2874, adaptiveSpanDenominator2874, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1437) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2874 adaptiveOrder2874 adaptiveSpanNumericCheck2874_4
        adaptiveSpanEven2874_4 adaptiveSpanWhole2874_4
        adaptiveSpanEvenEntries2874_4 adaptiveSpanWholeEntries2874_4
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanEvenDomain2874_4)
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanWholeDomain2874_4)
  · simpa only [adaptiveSpanLevel2874, adaptiveSpanNumerator2874, adaptiveSpanDenominator2874, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1437) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2874 adaptiveOrder2874 adaptiveSpanNumericCheck2874_5
        adaptiveSpanEven2874_5 adaptiveSpanWhole2874_5
        adaptiveSpanEvenEntries2874_5 adaptiveSpanWholeEntries2874_5
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanEvenDomain2874_5)
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanWholeDomain2874_5)
  · simpa only [adaptiveSpanLevel2874, adaptiveSpanNumerator2874, adaptiveSpanDenominator2874, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1437) (by decide : 0 < 437)
        adaptiveSpanProfilesValid2874 adaptiveOrder2874 adaptiveSpanNumericCheck2874_6
        adaptiveSpanEven2874_6 adaptiveSpanWhole2874_6
        adaptiveSpanEvenEntries2874_6 adaptiveSpanWholeEntries2874_6
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanEvenDomain2874_6)
        (by rw [adaptiveSpanProfileLength2874]; exact adaptiveSpanWholeDomain2874_6)

/-- The complete finite histogram certificate for 2738 ≤ n ≤ 2874. -/
theorem adaptiveSpanHistogram2874 : DegreeIntervalCertificate 2874 adaptiveSpanPrimes2874
    (fun s v => sharpDegree (2738 / 2) 7 (adaptiveSpanNumerator2874 s)
      (adaptiveSpanDenominator2874 s) (totientDensity v))
    (fun s v => sharpDegree 2738 7 (adaptiveSpanNumerator2874 s)
      (adaptiveSpanDenominator2874 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2874)
    adaptiveSpanPrimes2874
    (fun s => sharpDegree (2738 / 2) 7 (adaptiveSpanNumerator2874 s) (adaptiveSpanDenominator2874 s))
    (fun s => sharpDegree 2738 7 (adaptiveSpanNumerator2874 s) (adaptiveSpanDenominator2874 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2874 adaptiveOrder2874 (coreOrderPermutationCheck_sound adaptivePermutation2874)
    (by rw [adaptiveSpanProfileLength2874]; decide +kernel)
    adaptiveSpanLevel2874 adaptiveSpanTreeCache2874 adaptiveSpanTreeRepresents2874
    (fun j => adaptiveSpanWitness2874.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2874

/-- Every required odd cycle for a dense set, throughout 2738 ≤ n ≤ 2874. -/
theorem adaptiveSpanInterval2874 {n : ℕ} (hLn : 2738 ≤ n) (hnU : n ≤ 2874)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes2874
    adaptiveSpanNumerator2874 adaptiveSpanDenominator2874 adaptiveSpanSharpTail2874
    adaptiveSpanPrimeSupport2874 adaptiveSpanHistogram2874 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2874
#print axioms adaptiveSpanPrimeSupport2874
#print axioms adaptiveSpanHistogram2874
#print axioms adaptiveSpanInterval2874
end Erdos883Verified
