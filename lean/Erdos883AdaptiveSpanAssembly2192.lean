import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2192Metadata
import Erdos883AdaptiveSpan2192Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2192 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2192 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2192 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2192 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2192.length) :
    SharpTailCertificate 2192 (adaptiveSpanPrimes2192.take s)
      (adaptiveSpanNumerator2192 s) (adaptiveSpanDenominator2192 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2192 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2192 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2192 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2192 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2192 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2192 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2192 : ∀ u ∈ oddUniverse 2192,
    ∀ v ∈ oddUniverse 2192, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2192 : AdaptiveProfileRowsValid adaptiveRows2192 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2192

theorem adaptiveSpanProfileLength2192 : adaptiveRows2192.length = halfOdds 2192 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2192)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2192 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2192.length) :
    (adaptiveSpanLevel2192 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2192 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2192, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2192_0 adaptiveSpanWholeCache2192_0
  · simpa only [adaptiveSpanLevel2192, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2192_1 adaptiveSpanWholeCache2192_1
  · simpa only [adaptiveSpanLevel2192, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2192_2 adaptiveSpanWholeCache2192_2
  · simpa only [adaptiveSpanLevel2192, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2192_3 adaptiveSpanWholeCache2192_3
  · simpa only [adaptiveSpanLevel2192, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2192_4 adaptiveSpanWholeCache2192_4
  · simpa only [adaptiveSpanLevel2192, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2192_5 adaptiveSpanWholeCache2192_5

theorem adaptiveSpanTreeRepresents2192 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2192.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2192 (halfOdds 2192)
      (sharpDegree (2139 / 2) 6 (adaptiveSpanNumerator2192 s) (adaptiveSpanDenominator2192 s))
      (sharpDegree 2139 6 (adaptiveSpanNumerator2192 s) (adaptiveSpanDenominator2192 s))
      (adaptiveSpanLevel2192 s).1 (adaptiveSpanLevel2192 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2192, adaptiveSpanNumerator2192, adaptiveSpanDenominator2192, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1096) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2192 adaptiveOrder2192 adaptiveSpanNumericCheck2192_0
        adaptiveSpanEven2192_0 adaptiveSpanWhole2192_0
        adaptiveSpanEvenEntries2192_0 adaptiveSpanWholeEntries2192_0
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanEvenDomain2192_0)
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanWholeDomain2192_0)
  · simpa only [adaptiveSpanLevel2192, adaptiveSpanNumerator2192, adaptiveSpanDenominator2192, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1096) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2192 adaptiveOrder2192 adaptiveSpanNumericCheck2192_1
        adaptiveSpanEven2192_1 adaptiveSpanWhole2192_1
        adaptiveSpanEvenEntries2192_1 adaptiveSpanWholeEntries2192_1
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanEvenDomain2192_1)
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanWholeDomain2192_1)
  · simpa only [adaptiveSpanLevel2192, adaptiveSpanNumerator2192, adaptiveSpanDenominator2192, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1096) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2192 adaptiveOrder2192 adaptiveSpanNumericCheck2192_2
        adaptiveSpanEven2192_2 adaptiveSpanWhole2192_2
        adaptiveSpanEvenEntries2192_2 adaptiveSpanWholeEntries2192_2
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanEvenDomain2192_2)
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanWholeDomain2192_2)
  · simpa only [adaptiveSpanLevel2192, adaptiveSpanNumerator2192, adaptiveSpanDenominator2192, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1096) (by decide : 0 < 143)
        adaptiveSpanProfilesValid2192 adaptiveOrder2192 adaptiveSpanNumericCheck2192_3
        adaptiveSpanEven2192_3 adaptiveSpanWhole2192_3
        adaptiveSpanEvenEntries2192_3 adaptiveSpanWholeEntries2192_3
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanEvenDomain2192_3)
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanWholeDomain2192_3)
  · simpa only [adaptiveSpanLevel2192, adaptiveSpanNumerator2192, adaptiveSpanDenominator2192, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1096) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2192 adaptiveOrder2192 adaptiveSpanNumericCheck2192_4
        adaptiveSpanEven2192_4 adaptiveSpanWhole2192_4
        adaptiveSpanEvenEntries2192_4 adaptiveSpanWholeEntries2192_4
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanEvenDomain2192_4)
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanWholeDomain2192_4)
  · simpa only [adaptiveSpanLevel2192, adaptiveSpanNumerator2192, adaptiveSpanDenominator2192, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1096) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2192 adaptiveOrder2192 adaptiveSpanNumericCheck2192_5
        adaptiveSpanEven2192_5 adaptiveSpanWhole2192_5
        adaptiveSpanEvenEntries2192_5 adaptiveSpanWholeEntries2192_5
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanEvenDomain2192_5)
        (by rw [adaptiveSpanProfileLength2192]; exact adaptiveSpanWholeDomain2192_5)

/-- The complete finite histogram certificate for 2139 ≤ n ≤ 2192. -/
theorem adaptiveSpanHistogram2192 : DegreeIntervalCertificate 2192 adaptiveSpanPrimes2192
    (fun s v => sharpDegree (2139 / 2) 6 (adaptiveSpanNumerator2192 s)
      (adaptiveSpanDenominator2192 s) (totientDensity v))
    (fun s v => sharpDegree 2139 6 (adaptiveSpanNumerator2192 s)
      (adaptiveSpanDenominator2192 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2192)
    adaptiveSpanPrimes2192
    (fun s => sharpDegree (2139 / 2) 6 (adaptiveSpanNumerator2192 s) (adaptiveSpanDenominator2192 s))
    (fun s => sharpDegree 2139 6 (adaptiveSpanNumerator2192 s) (adaptiveSpanDenominator2192 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2192 adaptiveOrder2192 (coreOrderPermutationCheck_sound adaptivePermutation2192)
    (by rw [adaptiveSpanProfileLength2192]; decide +kernel)
    adaptiveSpanLevel2192 adaptiveSpanTreeCache2192 adaptiveSpanTreeRepresents2192
    (fun j => adaptiveSpanWitness2192.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2192

/-- Every required odd cycle for a dense set, throughout 2139 ≤ n ≤ 2192. -/
theorem adaptiveSpanInterval2192 {n : ℕ} (hLn : 2139 ≤ n) (hnU : n ≤ 2192)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes2192
    adaptiveSpanNumerator2192 adaptiveSpanDenominator2192 adaptiveSpanSharpTail2192
    adaptiveSpanPrimeSupport2192 adaptiveSpanHistogram2192 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2192
#print axioms adaptiveSpanPrimeSupport2192
#print axioms adaptiveSpanHistogram2192
#print axioms adaptiveSpanInterval2192
end Erdos883Verified
