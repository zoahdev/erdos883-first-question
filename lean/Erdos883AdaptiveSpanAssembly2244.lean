import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2244Metadata
import Erdos883AdaptiveSpan2244Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2244 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2244 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2244 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2244 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2244.length) :
    SharpTailCertificate 2244 (adaptiveSpanPrimes2244.take s)
      (adaptiveSpanNumerator2244 s) (adaptiveSpanDenominator2244 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2244 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2244 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2244 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2244 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2244 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2244 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2244 : ∀ u ∈ oddUniverse 2244,
    ∀ v ∈ oddUniverse 2244, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2244 : AdaptiveProfileRowsValid adaptiveRows2244 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2244

theorem adaptiveSpanProfileLength2244 : adaptiveRows2244.length = halfOdds 2244 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2244)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2244 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2244.length) :
    (adaptiveSpanLevel2244 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2244 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2244, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2244_0 adaptiveSpanWholeCache2244_0
  · simpa only [adaptiveSpanLevel2244, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2244_1 adaptiveSpanWholeCache2244_1
  · simpa only [adaptiveSpanLevel2244, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2244_2 adaptiveSpanWholeCache2244_2
  · simpa only [adaptiveSpanLevel2244, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2244_3 adaptiveSpanWholeCache2244_3
  · simpa only [adaptiveSpanLevel2244, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2244_4 adaptiveSpanWholeCache2244_4
  · simpa only [adaptiveSpanLevel2244, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2244_5 adaptiveSpanWholeCache2244_5

theorem adaptiveSpanTreeRepresents2244 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2244.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2244 (halfOdds 2244)
      (sharpDegree (2193 / 2) 7 (adaptiveSpanNumerator2244 s) (adaptiveSpanDenominator2244 s))
      (sharpDegree 2193 7 (adaptiveSpanNumerator2244 s) (adaptiveSpanDenominator2244 s))
      (adaptiveSpanLevel2244 s).1 (adaptiveSpanLevel2244 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2244, adaptiveSpanNumerator2244, adaptiveSpanDenominator2244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1122) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2244 adaptiveOrder2244 adaptiveSpanNumericCheck2244_0
        adaptiveSpanEven2244_0 adaptiveSpanWhole2244_0
        adaptiveSpanEvenEntries2244_0 adaptiveSpanWholeEntries2244_0
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanEvenDomain2244_0)
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanWholeDomain2244_0)
  · simpa only [adaptiveSpanLevel2244, adaptiveSpanNumerator2244, adaptiveSpanDenominator2244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1122) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2244 adaptiveOrder2244 adaptiveSpanNumericCheck2244_1
        adaptiveSpanEven2244_1 adaptiveSpanWhole2244_1
        adaptiveSpanEvenEntries2244_1 adaptiveSpanWholeEntries2244_1
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanEvenDomain2244_1)
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanWholeDomain2244_1)
  · simpa only [adaptiveSpanLevel2244, adaptiveSpanNumerator2244, adaptiveSpanDenominator2244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1122) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2244 adaptiveOrder2244 adaptiveSpanNumericCheck2244_2
        adaptiveSpanEven2244_2 adaptiveSpanWhole2244_2
        adaptiveSpanEvenEntries2244_2 adaptiveSpanWholeEntries2244_2
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanEvenDomain2244_2)
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanWholeDomain2244_2)
  · simpa only [adaptiveSpanLevel2244, adaptiveSpanNumerator2244, adaptiveSpanDenominator2244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1122) (by decide : 0 < 143)
        adaptiveSpanProfilesValid2244 adaptiveOrder2244 adaptiveSpanNumericCheck2244_3
        adaptiveSpanEven2244_3 adaptiveSpanWhole2244_3
        adaptiveSpanEvenEntries2244_3 adaptiveSpanWholeEntries2244_3
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanEvenDomain2244_3)
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanWholeDomain2244_3)
  · simpa only [adaptiveSpanLevel2244, adaptiveSpanNumerator2244, adaptiveSpanDenominator2244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1122) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2244 adaptiveOrder2244 adaptiveSpanNumericCheck2244_4
        adaptiveSpanEven2244_4 adaptiveSpanWhole2244_4
        adaptiveSpanEvenEntries2244_4 adaptiveSpanWholeEntries2244_4
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanEvenDomain2244_4)
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanWholeDomain2244_4)
  · simpa only [adaptiveSpanLevel2244, adaptiveSpanNumerator2244, adaptiveSpanDenominator2244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1122) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2244 adaptiveOrder2244 adaptiveSpanNumericCheck2244_5
        adaptiveSpanEven2244_5 adaptiveSpanWhole2244_5
        adaptiveSpanEvenEntries2244_5 adaptiveSpanWholeEntries2244_5
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanEvenDomain2244_5)
        (by rw [adaptiveSpanProfileLength2244]; exact adaptiveSpanWholeDomain2244_5)

/-- The complete finite histogram certificate for 2193 ≤ n ≤ 2244. -/
theorem adaptiveSpanHistogram2244 : DegreeIntervalCertificate 2244 adaptiveSpanPrimes2244
    (fun s v => sharpDegree (2193 / 2) 7 (adaptiveSpanNumerator2244 s)
      (adaptiveSpanDenominator2244 s) (totientDensity v))
    (fun s v => sharpDegree 2193 7 (adaptiveSpanNumerator2244 s)
      (adaptiveSpanDenominator2244 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2244)
    adaptiveSpanPrimes2244
    (fun s => sharpDegree (2193 / 2) 7 (adaptiveSpanNumerator2244 s) (adaptiveSpanDenominator2244 s))
    (fun s => sharpDegree 2193 7 (adaptiveSpanNumerator2244 s) (adaptiveSpanDenominator2244 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2244 adaptiveOrder2244 (coreOrderPermutationCheck_sound adaptivePermutation2244)
    (by rw [adaptiveSpanProfileLength2244]; decide +kernel)
    adaptiveSpanLevel2244 adaptiveSpanTreeCache2244 adaptiveSpanTreeRepresents2244
    (fun j => adaptiveSpanWitness2244.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2244

/-- Every required odd cycle for a dense set, throughout 2193 ≤ n ≤ 2244. -/
theorem adaptiveSpanInterval2244 {n : ℕ} (hLn : 2193 ≤ n) (hnU : n ≤ 2244)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes2244
    adaptiveSpanNumerator2244 adaptiveSpanDenominator2244 adaptiveSpanSharpTail2244
    adaptiveSpanPrimeSupport2244 adaptiveSpanHistogram2244 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2244
#print axioms adaptiveSpanPrimeSupport2244
#print axioms adaptiveSpanHistogram2244
#print axioms adaptiveSpanInterval2244
end Erdos883Verified
