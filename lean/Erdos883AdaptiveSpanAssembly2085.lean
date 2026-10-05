import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2085Metadata
import Erdos883AdaptiveSpan2085Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2085 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2085 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2085 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2085 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2085.length) :
    SharpTailCertificate 2085 (adaptiveSpanPrimes2085.take s)
      (adaptiveSpanNumerator2085 s) (adaptiveSpanDenominator2085 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2085 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2085 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2085 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2085 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2085 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2085 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2085 : ∀ u ∈ oddUniverse 2085,
    ∀ v ∈ oddUniverse 2085, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2085 : AdaptiveProfileRowsValid adaptiveRows2085 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2085

theorem adaptiveSpanProfileLength2085 : adaptiveRows2085.length = halfOdds 2085 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2085)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2085 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2085.length) :
    (adaptiveSpanLevel2085 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2085 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2085, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2085_0 adaptiveSpanWholeCache2085_0
  · simpa only [adaptiveSpanLevel2085, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2085_1 adaptiveSpanWholeCache2085_1
  · simpa only [adaptiveSpanLevel2085, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2085_2 adaptiveSpanWholeCache2085_2
  · simpa only [adaptiveSpanLevel2085, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2085_3 adaptiveSpanWholeCache2085_3
  · simpa only [adaptiveSpanLevel2085, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2085_4 adaptiveSpanWholeCache2085_4
  · simpa only [adaptiveSpanLevel2085, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2085_5 adaptiveSpanWholeCache2085_5

theorem adaptiveSpanTreeRepresents2085 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2085.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2085 (halfOdds 2085)
      (sharpDegree (2035 / 2) 6 (adaptiveSpanNumerator2085 s) (adaptiveSpanDenominator2085 s))
      (sharpDegree 2035 6 (adaptiveSpanNumerator2085 s) (adaptiveSpanDenominator2085 s))
      (adaptiveSpanLevel2085 s).1 (adaptiveSpanLevel2085 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2085, adaptiveSpanNumerator2085, adaptiveSpanDenominator2085, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1043) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2085 adaptiveOrder2085 adaptiveSpanNumericCheck2085_0
        adaptiveSpanEven2085_0 adaptiveSpanWhole2085_0
        adaptiveSpanEvenEntries2085_0 adaptiveSpanWholeEntries2085_0
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanEvenDomain2085_0)
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanWholeDomain2085_0)
  · simpa only [adaptiveSpanLevel2085, adaptiveSpanNumerator2085, adaptiveSpanDenominator2085, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1043) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2085 adaptiveOrder2085 adaptiveSpanNumericCheck2085_1
        adaptiveSpanEven2085_1 adaptiveSpanWhole2085_1
        adaptiveSpanEvenEntries2085_1 adaptiveSpanWholeEntries2085_1
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanEvenDomain2085_1)
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanWholeDomain2085_1)
  · simpa only [adaptiveSpanLevel2085, adaptiveSpanNumerator2085, adaptiveSpanDenominator2085, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1043) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2085 adaptiveOrder2085 adaptiveSpanNumericCheck2085_2
        adaptiveSpanEven2085_2 adaptiveSpanWhole2085_2
        adaptiveSpanEvenEntries2085_2 adaptiveSpanWholeEntries2085_2
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanEvenDomain2085_2)
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanWholeDomain2085_2)
  · simpa only [adaptiveSpanLevel2085, adaptiveSpanNumerator2085, adaptiveSpanDenominator2085, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1043) (by decide : 0 < 143)
        adaptiveSpanProfilesValid2085 adaptiveOrder2085 adaptiveSpanNumericCheck2085_3
        adaptiveSpanEven2085_3 adaptiveSpanWhole2085_3
        adaptiveSpanEvenEntries2085_3 adaptiveSpanWholeEntries2085_3
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanEvenDomain2085_3)
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanWholeDomain2085_3)
  · simpa only [adaptiveSpanLevel2085, adaptiveSpanNumerator2085, adaptiveSpanDenominator2085, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1043) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2085 adaptiveOrder2085 adaptiveSpanNumericCheck2085_4
        adaptiveSpanEven2085_4 adaptiveSpanWhole2085_4
        adaptiveSpanEvenEntries2085_4 adaptiveSpanWholeEntries2085_4
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanEvenDomain2085_4)
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanWholeDomain2085_4)
  · simpa only [adaptiveSpanLevel2085, adaptiveSpanNumerator2085, adaptiveSpanDenominator2085, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1043) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2085 adaptiveOrder2085 adaptiveSpanNumericCheck2085_5
        adaptiveSpanEven2085_5 adaptiveSpanWhole2085_5
        adaptiveSpanEvenEntries2085_5 adaptiveSpanWholeEntries2085_5
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanEvenDomain2085_5)
        (by rw [adaptiveSpanProfileLength2085]; exact adaptiveSpanWholeDomain2085_5)

/-- The complete finite histogram certificate for 2035 ≤ n ≤ 2085. -/
theorem adaptiveSpanHistogram2085 : DegreeIntervalCertificate 2085 adaptiveSpanPrimes2085
    (fun s v => sharpDegree (2035 / 2) 6 (adaptiveSpanNumerator2085 s)
      (adaptiveSpanDenominator2085 s) (totientDensity v))
    (fun s v => sharpDegree 2035 6 (adaptiveSpanNumerator2085 s)
      (adaptiveSpanDenominator2085 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2085)
    adaptiveSpanPrimes2085
    (fun s => sharpDegree (2035 / 2) 6 (adaptiveSpanNumerator2085 s) (adaptiveSpanDenominator2085 s))
    (fun s => sharpDegree 2035 6 (adaptiveSpanNumerator2085 s) (adaptiveSpanDenominator2085 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2085 adaptiveOrder2085 (coreOrderPermutationCheck_sound adaptivePermutation2085)
    (by rw [adaptiveSpanProfileLength2085]; decide +kernel)
    adaptiveSpanLevel2085 adaptiveSpanTreeCache2085 adaptiveSpanTreeRepresents2085
    (fun j => adaptiveSpanWitness2085.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2085

/-- Every required odd cycle for a dense set, throughout 2035 ≤ n ≤ 2085. -/
theorem adaptiveSpanInterval2085 {n : ℕ} (hLn : 2035 ≤ n) (hnU : n ≤ 2085)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes2085
    adaptiveSpanNumerator2085 adaptiveSpanDenominator2085 adaptiveSpanSharpTail2085
    adaptiveSpanPrimeSupport2085 adaptiveSpanHistogram2085 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2085
#print axioms adaptiveSpanPrimeSupport2085
#print axioms adaptiveSpanHistogram2085
#print axioms adaptiveSpanInterval2085
end Erdos883Verified
