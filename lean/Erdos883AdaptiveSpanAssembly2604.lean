import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2604Metadata
import Erdos883AdaptiveSpan2604Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2604 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2604 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2604 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2604 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2604.length) :
    SharpTailCertificate 2604 (adaptiveSpanPrimes2604.take s)
      (adaptiveSpanNumerator2604 s) (adaptiveSpanDenominator2604 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2604 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2604 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2604 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2604 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2604 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2604 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2604 : ∀ u ∈ oddUniverse 2604,
    ∀ v ∈ oddUniverse 2604, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2604 : AdaptiveProfileRowsValid adaptiveRows2604 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2604

theorem adaptiveSpanProfileLength2604 : adaptiveRows2604.length = halfOdds 2604 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2604)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2604 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2604.length) :
    (adaptiveSpanLevel2604 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2604 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2604, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2604_0 adaptiveSpanWholeCache2604_0
  · simpa only [adaptiveSpanLevel2604, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2604_1 adaptiveSpanWholeCache2604_1
  · simpa only [adaptiveSpanLevel2604, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2604_2 adaptiveSpanWholeCache2604_2
  · simpa only [adaptiveSpanLevel2604, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2604_3 adaptiveSpanWholeCache2604_3
  · simpa only [adaptiveSpanLevel2604, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2604_4 adaptiveSpanWholeCache2604_4
  · simpa only [adaptiveSpanLevel2604, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2604_5 adaptiveSpanWholeCache2604_5

theorem adaptiveSpanTreeRepresents2604 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2604.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2604 (halfOdds 2604)
      (sharpDegree (2541 / 2) 7 (adaptiveSpanNumerator2604 s) (adaptiveSpanDenominator2604 s))
      (sharpDegree 2541 7 (adaptiveSpanNumerator2604 s) (adaptiveSpanDenominator2604 s))
      (adaptiveSpanLevel2604 s).1 (adaptiveSpanLevel2604 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2604, adaptiveSpanNumerator2604, adaptiveSpanDenominator2604, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1302) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2604 adaptiveOrder2604 adaptiveSpanNumericCheck2604_0
        adaptiveSpanEven2604_0 adaptiveSpanWhole2604_0
        adaptiveSpanEvenEntries2604_0 adaptiveSpanWholeEntries2604_0
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanEvenDomain2604_0)
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanWholeDomain2604_0)
  · simpa only [adaptiveSpanLevel2604, adaptiveSpanNumerator2604, adaptiveSpanDenominator2604, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1302) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2604 adaptiveOrder2604 adaptiveSpanNumericCheck2604_1
        adaptiveSpanEven2604_1 adaptiveSpanWhole2604_1
        adaptiveSpanEvenEntries2604_1 adaptiveSpanWholeEntries2604_1
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanEvenDomain2604_1)
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanWholeDomain2604_1)
  · simpa only [adaptiveSpanLevel2604, adaptiveSpanNumerator2604, adaptiveSpanDenominator2604, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1302) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2604 adaptiveOrder2604 adaptiveSpanNumericCheck2604_2
        adaptiveSpanEven2604_2 adaptiveSpanWhole2604_2
        adaptiveSpanEvenEntries2604_2 adaptiveSpanWholeEntries2604_2
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanEvenDomain2604_2)
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanWholeDomain2604_2)
  · simpa only [adaptiveSpanLevel2604, adaptiveSpanNumerator2604, adaptiveSpanDenominator2604, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1302) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid2604 adaptiveOrder2604 adaptiveSpanNumericCheck2604_3
        adaptiveSpanEven2604_3 adaptiveSpanWhole2604_3
        adaptiveSpanEvenEntries2604_3 adaptiveSpanWholeEntries2604_3
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanEvenDomain2604_3)
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanWholeDomain2604_3)
  · simpa only [adaptiveSpanLevel2604, adaptiveSpanNumerator2604, adaptiveSpanDenominator2604, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1302) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2604 adaptiveOrder2604 adaptiveSpanNumericCheck2604_4
        adaptiveSpanEven2604_4 adaptiveSpanWhole2604_4
        adaptiveSpanEvenEntries2604_4 adaptiveSpanWholeEntries2604_4
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanEvenDomain2604_4)
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanWholeDomain2604_4)
  · simpa only [adaptiveSpanLevel2604, adaptiveSpanNumerator2604, adaptiveSpanDenominator2604, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1302) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2604 adaptiveOrder2604 adaptiveSpanNumericCheck2604_5
        adaptiveSpanEven2604_5 adaptiveSpanWhole2604_5
        adaptiveSpanEvenEntries2604_5 adaptiveSpanWholeEntries2604_5
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanEvenDomain2604_5)
        (by rw [adaptiveSpanProfileLength2604]; exact adaptiveSpanWholeDomain2604_5)

/-- The complete finite histogram certificate for 2541 ≤ n ≤ 2604. -/
theorem adaptiveSpanHistogram2604 : DegreeIntervalCertificate 2604 adaptiveSpanPrimes2604
    (fun s v => sharpDegree (2541 / 2) 7 (adaptiveSpanNumerator2604 s)
      (adaptiveSpanDenominator2604 s) (totientDensity v))
    (fun s v => sharpDegree 2541 7 (adaptiveSpanNumerator2604 s)
      (adaptiveSpanDenominator2604 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2604)
    adaptiveSpanPrimes2604
    (fun s => sharpDegree (2541 / 2) 7 (adaptiveSpanNumerator2604 s) (adaptiveSpanDenominator2604 s))
    (fun s => sharpDegree 2541 7 (adaptiveSpanNumerator2604 s) (adaptiveSpanDenominator2604 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2604 adaptiveOrder2604 (coreOrderPermutationCheck_sound adaptivePermutation2604)
    (by rw [adaptiveSpanProfileLength2604]; decide +kernel)
    adaptiveSpanLevel2604 adaptiveSpanTreeCache2604 adaptiveSpanTreeRepresents2604
    (fun j => adaptiveSpanWitness2604.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2604

/-- Every required odd cycle for a dense set, throughout 2541 ≤ n ≤ 2604. -/
theorem adaptiveSpanInterval2604 {n : ℕ} (hLn : 2541 ≤ n) (hnU : n ≤ 2604)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes2604
    adaptiveSpanNumerator2604 adaptiveSpanDenominator2604 adaptiveSpanSharpTail2604
    adaptiveSpanPrimeSupport2604 adaptiveSpanHistogram2604 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2604
#print axioms adaptiveSpanPrimeSupport2604
#print axioms adaptiveSpanHistogram2604
#print axioms adaptiveSpanInterval2604
end Erdos883Verified
