import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2138Metadata
import Erdos883AdaptiveSpan2138Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2138 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2138 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2138 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2138 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2138.length) :
    SharpTailCertificate 2138 (adaptiveSpanPrimes2138.take s)
      (adaptiveSpanNumerator2138 s) (adaptiveSpanDenominator2138 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2138 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2138 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2138 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2138 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2138 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2138 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2138 : ∀ u ∈ oddUniverse 2138,
    ∀ v ∈ oddUniverse 2138, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2138 : AdaptiveProfileRowsValid adaptiveRows2138 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2138

theorem adaptiveSpanProfileLength2138 : adaptiveRows2138.length = halfOdds 2138 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2138)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2138 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2138.length) :
    (adaptiveSpanLevel2138 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2138 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2138, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2138_0 adaptiveSpanWholeCache2138_0
  · simpa only [adaptiveSpanLevel2138, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2138_1 adaptiveSpanWholeCache2138_1
  · simpa only [adaptiveSpanLevel2138, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2138_2 adaptiveSpanWholeCache2138_2
  · simpa only [adaptiveSpanLevel2138, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2138_3 adaptiveSpanWholeCache2138_3
  · simpa only [adaptiveSpanLevel2138, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2138_4 adaptiveSpanWholeCache2138_4
  · simpa only [adaptiveSpanLevel2138, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2138_5 adaptiveSpanWholeCache2138_5

theorem adaptiveSpanTreeRepresents2138 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2138.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2138 (halfOdds 2138)
      (sharpDegree (2086 / 2) 6 (adaptiveSpanNumerator2138 s) (adaptiveSpanDenominator2138 s))
      (sharpDegree 2086 6 (adaptiveSpanNumerator2138 s) (adaptiveSpanDenominator2138 s))
      (adaptiveSpanLevel2138 s).1 (adaptiveSpanLevel2138 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2138, adaptiveSpanNumerator2138, adaptiveSpanDenominator2138, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1069) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2138 adaptiveOrder2138 adaptiveSpanNumericCheck2138_0
        adaptiveSpanEven2138_0 adaptiveSpanWhole2138_0
        adaptiveSpanEvenEntries2138_0 adaptiveSpanWholeEntries2138_0
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanEvenDomain2138_0)
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanWholeDomain2138_0)
  · simpa only [adaptiveSpanLevel2138, adaptiveSpanNumerator2138, adaptiveSpanDenominator2138, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1069) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2138 adaptiveOrder2138 adaptiveSpanNumericCheck2138_1
        adaptiveSpanEven2138_1 adaptiveSpanWhole2138_1
        adaptiveSpanEvenEntries2138_1 adaptiveSpanWholeEntries2138_1
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanEvenDomain2138_1)
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanWholeDomain2138_1)
  · simpa only [adaptiveSpanLevel2138, adaptiveSpanNumerator2138, adaptiveSpanDenominator2138, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1069) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2138 adaptiveOrder2138 adaptiveSpanNumericCheck2138_2
        adaptiveSpanEven2138_2 adaptiveSpanWhole2138_2
        adaptiveSpanEvenEntries2138_2 adaptiveSpanWholeEntries2138_2
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanEvenDomain2138_2)
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanWholeDomain2138_2)
  · simpa only [adaptiveSpanLevel2138, adaptiveSpanNumerator2138, adaptiveSpanDenominator2138, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1069) (by decide : 0 < 143)
        adaptiveSpanProfilesValid2138 adaptiveOrder2138 adaptiveSpanNumericCheck2138_3
        adaptiveSpanEven2138_3 adaptiveSpanWhole2138_3
        adaptiveSpanEvenEntries2138_3 adaptiveSpanWholeEntries2138_3
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanEvenDomain2138_3)
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanWholeDomain2138_3)
  · simpa only [adaptiveSpanLevel2138, adaptiveSpanNumerator2138, adaptiveSpanDenominator2138, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1069) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2138 adaptiveOrder2138 adaptiveSpanNumericCheck2138_4
        adaptiveSpanEven2138_4 adaptiveSpanWhole2138_4
        adaptiveSpanEvenEntries2138_4 adaptiveSpanWholeEntries2138_4
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanEvenDomain2138_4)
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanWholeDomain2138_4)
  · simpa only [adaptiveSpanLevel2138, adaptiveSpanNumerator2138, adaptiveSpanDenominator2138, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1069) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2138 adaptiveOrder2138 adaptiveSpanNumericCheck2138_5
        adaptiveSpanEven2138_5 adaptiveSpanWhole2138_5
        adaptiveSpanEvenEntries2138_5 adaptiveSpanWholeEntries2138_5
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanEvenDomain2138_5)
        (by rw [adaptiveSpanProfileLength2138]; exact adaptiveSpanWholeDomain2138_5)

/-- The complete finite histogram certificate for 2086 ≤ n ≤ 2138. -/
theorem adaptiveSpanHistogram2138 : DegreeIntervalCertificate 2138 adaptiveSpanPrimes2138
    (fun s v => sharpDegree (2086 / 2) 6 (adaptiveSpanNumerator2138 s)
      (adaptiveSpanDenominator2138 s) (totientDensity v))
    (fun s v => sharpDegree 2086 6 (adaptiveSpanNumerator2138 s)
      (adaptiveSpanDenominator2138 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2138)
    adaptiveSpanPrimes2138
    (fun s => sharpDegree (2086 / 2) 6 (adaptiveSpanNumerator2138 s) (adaptiveSpanDenominator2138 s))
    (fun s => sharpDegree 2086 6 (adaptiveSpanNumerator2138 s) (adaptiveSpanDenominator2138 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2138 adaptiveOrder2138 (coreOrderPermutationCheck_sound adaptivePermutation2138)
    (by rw [adaptiveSpanProfileLength2138]; decide +kernel)
    adaptiveSpanLevel2138 adaptiveSpanTreeCache2138 adaptiveSpanTreeRepresents2138
    (fun j => adaptiveSpanWitness2138.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2138

/-- Every required odd cycle for a dense set, throughout 2086 ≤ n ≤ 2138. -/
theorem adaptiveSpanInterval2138 {n : ℕ} (hLn : 2086 ≤ n) (hnU : n ≤ 2138)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes2138
    adaptiveSpanNumerator2138 adaptiveSpanDenominator2138 adaptiveSpanSharpTail2138
    adaptiveSpanPrimeSupport2138 adaptiveSpanHistogram2138 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2138
#print axioms adaptiveSpanPrimeSupport2138
#print axioms adaptiveSpanHistogram2138
#print axioms adaptiveSpanInterval2138
end Erdos883Verified
