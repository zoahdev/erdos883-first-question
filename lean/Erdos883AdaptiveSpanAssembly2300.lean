import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2300Metadata
import Erdos883AdaptiveSpan2300Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2300 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2300 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2300 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2300 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2300.length) :
    SharpTailCertificate 2300 (adaptiveSpanPrimes2300.take s)
      (adaptiveSpanNumerator2300 s) (adaptiveSpanDenominator2300 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2300 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2300 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2300 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2300 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2300 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2300 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2300 : ∀ u ∈ oddUniverse 2300,
    ∀ v ∈ oddUniverse 2300, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2300 : AdaptiveProfileRowsValid adaptiveRows2300 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2300

theorem adaptiveSpanProfileLength2300 : adaptiveRows2300.length = halfOdds 2300 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2300)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2300 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2300.length) :
    (adaptiveSpanLevel2300 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2300 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2300, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2300_0 adaptiveSpanWholeCache2300_0
  · simpa only [adaptiveSpanLevel2300, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2300_1 adaptiveSpanWholeCache2300_1
  · simpa only [adaptiveSpanLevel2300, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2300_2 adaptiveSpanWholeCache2300_2
  · simpa only [adaptiveSpanLevel2300, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2300_3 adaptiveSpanWholeCache2300_3
  · simpa only [adaptiveSpanLevel2300, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2300_4 adaptiveSpanWholeCache2300_4
  · simpa only [adaptiveSpanLevel2300, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2300_5 adaptiveSpanWholeCache2300_5

theorem adaptiveSpanTreeRepresents2300 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2300.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2300 (halfOdds 2300)
      (sharpDegree (2245 / 2) 7 (adaptiveSpanNumerator2300 s) (adaptiveSpanDenominator2300 s))
      (sharpDegree 2245 7 (adaptiveSpanNumerator2300 s) (adaptiveSpanDenominator2300 s))
      (adaptiveSpanLevel2300 s).1 (adaptiveSpanLevel2300 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2300, adaptiveSpanNumerator2300, adaptiveSpanDenominator2300, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1150) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2300 adaptiveOrder2300 adaptiveSpanNumericCheck2300_0
        adaptiveSpanEven2300_0 adaptiveSpanWhole2300_0
        adaptiveSpanEvenEntries2300_0 adaptiveSpanWholeEntries2300_0
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanEvenDomain2300_0)
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanWholeDomain2300_0)
  · simpa only [adaptiveSpanLevel2300, adaptiveSpanNumerator2300, adaptiveSpanDenominator2300, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1150) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2300 adaptiveOrder2300 adaptiveSpanNumericCheck2300_1
        adaptiveSpanEven2300_1 adaptiveSpanWhole2300_1
        adaptiveSpanEvenEntries2300_1 adaptiveSpanWholeEntries2300_1
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanEvenDomain2300_1)
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanWholeDomain2300_1)
  · simpa only [adaptiveSpanLevel2300, adaptiveSpanNumerator2300, adaptiveSpanDenominator2300, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1150) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2300 adaptiveOrder2300 adaptiveSpanNumericCheck2300_2
        adaptiveSpanEven2300_2 adaptiveSpanWhole2300_2
        adaptiveSpanEvenEntries2300_2 adaptiveSpanWholeEntries2300_2
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanEvenDomain2300_2)
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanWholeDomain2300_2)
  · simpa only [adaptiveSpanLevel2300, adaptiveSpanNumerator2300, adaptiveSpanDenominator2300, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1150) (by decide : 0 < 143)
        adaptiveSpanProfilesValid2300 adaptiveOrder2300 adaptiveSpanNumericCheck2300_3
        adaptiveSpanEven2300_3 adaptiveSpanWhole2300_3
        adaptiveSpanEvenEntries2300_3 adaptiveSpanWholeEntries2300_3
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanEvenDomain2300_3)
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanWholeDomain2300_3)
  · simpa only [adaptiveSpanLevel2300, adaptiveSpanNumerator2300, adaptiveSpanDenominator2300, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1150) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2300 adaptiveOrder2300 adaptiveSpanNumericCheck2300_4
        adaptiveSpanEven2300_4 adaptiveSpanWhole2300_4
        adaptiveSpanEvenEntries2300_4 adaptiveSpanWholeEntries2300_4
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanEvenDomain2300_4)
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanWholeDomain2300_4)
  · simpa only [adaptiveSpanLevel2300, adaptiveSpanNumerator2300, adaptiveSpanDenominator2300, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1150) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2300 adaptiveOrder2300 adaptiveSpanNumericCheck2300_5
        adaptiveSpanEven2300_5 adaptiveSpanWhole2300_5
        adaptiveSpanEvenEntries2300_5 adaptiveSpanWholeEntries2300_5
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanEvenDomain2300_5)
        (by rw [adaptiveSpanProfileLength2300]; exact adaptiveSpanWholeDomain2300_5)

/-- The complete finite histogram certificate for 2245 ≤ n ≤ 2300. -/
theorem adaptiveSpanHistogram2300 : DegreeIntervalCertificate 2300 adaptiveSpanPrimes2300
    (fun s v => sharpDegree (2245 / 2) 7 (adaptiveSpanNumerator2300 s)
      (adaptiveSpanDenominator2300 s) (totientDensity v))
    (fun s v => sharpDegree 2245 7 (adaptiveSpanNumerator2300 s)
      (adaptiveSpanDenominator2300 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2300)
    adaptiveSpanPrimes2300
    (fun s => sharpDegree (2245 / 2) 7 (adaptiveSpanNumerator2300 s) (adaptiveSpanDenominator2300 s))
    (fun s => sharpDegree 2245 7 (adaptiveSpanNumerator2300 s) (adaptiveSpanDenominator2300 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2300 adaptiveOrder2300 (coreOrderPermutationCheck_sound adaptivePermutation2300)
    (by rw [adaptiveSpanProfileLength2300]; decide +kernel)
    adaptiveSpanLevel2300 adaptiveSpanTreeCache2300 adaptiveSpanTreeRepresents2300
    (fun j => adaptiveSpanWitness2300.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2300

/-- Every required odd cycle for a dense set, throughout 2245 ≤ n ≤ 2300. -/
theorem adaptiveSpanInterval2300 {n : ℕ} (hLn : 2245 ≤ n) (hnU : n ≤ 2300)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes2300
    adaptiveSpanNumerator2300 adaptiveSpanDenominator2300 adaptiveSpanSharpTail2300
    adaptiveSpanPrimeSupport2300 adaptiveSpanHistogram2300 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2300
#print axioms adaptiveSpanPrimeSupport2300
#print axioms adaptiveSpanHistogram2300
#print axioms adaptiveSpanInterval2300
end Erdos883Verified
