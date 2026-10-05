import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2358Metadata
import Erdos883AdaptiveSpan2358Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2358 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2358 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2358 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2358 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2358.length) :
    SharpTailCertificate 2358 (adaptiveSpanPrimes2358.take s)
      (adaptiveSpanNumerator2358 s) (adaptiveSpanDenominator2358 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2358 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2358 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2358 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2358 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2358 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2358 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2358 : ∀ u ∈ oddUniverse 2358,
    ∀ v ∈ oddUniverse 2358, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2358 : AdaptiveProfileRowsValid adaptiveRows2358 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2358

theorem adaptiveSpanProfileLength2358 : adaptiveRows2358.length = halfOdds 2358 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2358)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2358 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2358.length) :
    (adaptiveSpanLevel2358 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2358 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2358, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2358_0 adaptiveSpanWholeCache2358_0
  · simpa only [adaptiveSpanLevel2358, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2358_1 adaptiveSpanWholeCache2358_1
  · simpa only [adaptiveSpanLevel2358, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2358_2 adaptiveSpanWholeCache2358_2
  · simpa only [adaptiveSpanLevel2358, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2358_3 adaptiveSpanWholeCache2358_3
  · simpa only [adaptiveSpanLevel2358, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2358_4 adaptiveSpanWholeCache2358_4
  · simpa only [adaptiveSpanLevel2358, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2358_5 adaptiveSpanWholeCache2358_5

theorem adaptiveSpanTreeRepresents2358 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2358.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2358 (halfOdds 2358)
      (sharpDegree (2301 / 2) 7 (adaptiveSpanNumerator2358 s) (adaptiveSpanDenominator2358 s))
      (sharpDegree 2301 7 (adaptiveSpanNumerator2358 s) (adaptiveSpanDenominator2358 s))
      (adaptiveSpanLevel2358 s).1 (adaptiveSpanLevel2358 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2358, adaptiveSpanNumerator2358, adaptiveSpanDenominator2358, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1179) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2358 adaptiveOrder2358 adaptiveSpanNumericCheck2358_0
        adaptiveSpanEven2358_0 adaptiveSpanWhole2358_0
        adaptiveSpanEvenEntries2358_0 adaptiveSpanWholeEntries2358_0
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanEvenDomain2358_0)
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanWholeDomain2358_0)
  · simpa only [adaptiveSpanLevel2358, adaptiveSpanNumerator2358, adaptiveSpanDenominator2358, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1179) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2358 adaptiveOrder2358 adaptiveSpanNumericCheck2358_1
        adaptiveSpanEven2358_1 adaptiveSpanWhole2358_1
        adaptiveSpanEvenEntries2358_1 adaptiveSpanWholeEntries2358_1
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanEvenDomain2358_1)
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanWholeDomain2358_1)
  · simpa only [adaptiveSpanLevel2358, adaptiveSpanNumerator2358, adaptiveSpanDenominator2358, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1179) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2358 adaptiveOrder2358 adaptiveSpanNumericCheck2358_2
        adaptiveSpanEven2358_2 adaptiveSpanWhole2358_2
        adaptiveSpanEvenEntries2358_2 adaptiveSpanWholeEntries2358_2
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanEvenDomain2358_2)
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanWholeDomain2358_2)
  · simpa only [adaptiveSpanLevel2358, adaptiveSpanNumerator2358, adaptiveSpanDenominator2358, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1179) (by decide : 0 < 143)
        adaptiveSpanProfilesValid2358 adaptiveOrder2358 adaptiveSpanNumericCheck2358_3
        adaptiveSpanEven2358_3 adaptiveSpanWhole2358_3
        adaptiveSpanEvenEntries2358_3 adaptiveSpanWholeEntries2358_3
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanEvenDomain2358_3)
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanWholeDomain2358_3)
  · simpa only [adaptiveSpanLevel2358, adaptiveSpanNumerator2358, adaptiveSpanDenominator2358, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1179) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2358 adaptiveOrder2358 adaptiveSpanNumericCheck2358_4
        adaptiveSpanEven2358_4 adaptiveSpanWhole2358_4
        adaptiveSpanEvenEntries2358_4 adaptiveSpanWholeEntries2358_4
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanEvenDomain2358_4)
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanWholeDomain2358_4)
  · simpa only [adaptiveSpanLevel2358, adaptiveSpanNumerator2358, adaptiveSpanDenominator2358, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1179) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2358 adaptiveOrder2358 adaptiveSpanNumericCheck2358_5
        adaptiveSpanEven2358_5 adaptiveSpanWhole2358_5
        adaptiveSpanEvenEntries2358_5 adaptiveSpanWholeEntries2358_5
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanEvenDomain2358_5)
        (by rw [adaptiveSpanProfileLength2358]; exact adaptiveSpanWholeDomain2358_5)

/-- The complete finite histogram certificate for 2301 ≤ n ≤ 2358. -/
theorem adaptiveSpanHistogram2358 : DegreeIntervalCertificate 2358 adaptiveSpanPrimes2358
    (fun s v => sharpDegree (2301 / 2) 7 (adaptiveSpanNumerator2358 s)
      (adaptiveSpanDenominator2358 s) (totientDensity v))
    (fun s v => sharpDegree 2301 7 (adaptiveSpanNumerator2358 s)
      (adaptiveSpanDenominator2358 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2358)
    adaptiveSpanPrimes2358
    (fun s => sharpDegree (2301 / 2) 7 (adaptiveSpanNumerator2358 s) (adaptiveSpanDenominator2358 s))
    (fun s => sharpDegree 2301 7 (adaptiveSpanNumerator2358 s) (adaptiveSpanDenominator2358 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2358 adaptiveOrder2358 (coreOrderPermutationCheck_sound adaptivePermutation2358)
    (by rw [adaptiveSpanProfileLength2358]; decide +kernel)
    adaptiveSpanLevel2358 adaptiveSpanTreeCache2358 adaptiveSpanTreeRepresents2358
    (fun j => adaptiveSpanWitness2358.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2358

/-- Every required odd cycle for a dense set, throughout 2301 ≤ n ≤ 2358. -/
theorem adaptiveSpanInterval2358 {n : ℕ} (hLn : 2301 ≤ n) (hnU : n ≤ 2358)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes2358
    adaptiveSpanNumerator2358 adaptiveSpanDenominator2358 adaptiveSpanSharpTail2358
    adaptiveSpanPrimeSupport2358 adaptiveSpanHistogram2358 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2358
#print axioms adaptiveSpanPrimeSupport2358
#print axioms adaptiveSpanHistogram2358
#print axioms adaptiveSpanInterval2358
end Erdos883Verified
