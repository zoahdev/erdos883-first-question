import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate2737Metadata
import Erdos883AdaptiveSpan2737Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes2737 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator2737 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator2737 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail2737 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2737.length) :
    SharpTailCertificate 2737 (adaptiveSpanPrimes2737.take s)
      (adaptiveSpanNumerator2737 s) (adaptiveSpanDenominator2737 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2737 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2737 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2737 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2737 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2737 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2737 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport2737 : ∀ u ∈ oddUniverse 2737,
    ∀ v ∈ oddUniverse 2737, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid2737 : AdaptiveProfileRowsValid adaptiveRows2737 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2737

theorem adaptiveSpanProfileLength2737 : adaptiveRows2737.length = halfOdds 2737 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation2737)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache2737 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2737.length) :
    (adaptiveSpanLevel2737 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel2737 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2737, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2737_0 adaptiveSpanWholeCache2737_0
  · simpa only [adaptiveSpanLevel2737, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2737_1 adaptiveSpanWholeCache2737_1
  · simpa only [adaptiveSpanLevel2737, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2737_2 adaptiveSpanWholeCache2737_2
  · simpa only [adaptiveSpanLevel2737, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2737_3 adaptiveSpanWholeCache2737_3
  · simpa only [adaptiveSpanLevel2737, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2737_4 adaptiveSpanWholeCache2737_4
  · simpa only [adaptiveSpanLevel2737, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache2737_5 adaptiveSpanWholeCache2737_5

theorem adaptiveSpanTreeRepresents2737 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes2737.length) :
    AdaptiveSpanTreeRepresents adaptiveRows2737 (halfOdds 2737)
      (sharpDegree (2671 / 2) 7 (adaptiveSpanNumerator2737 s) (adaptiveSpanDenominator2737 s))
      (sharpDegree 2671 7 (adaptiveSpanNumerator2737 s) (adaptiveSpanDenominator2737 s))
      (adaptiveSpanLevel2737 s).1 (adaptiveSpanLevel2737 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel2737, adaptiveSpanNumerator2737, adaptiveSpanDenominator2737, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1369) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid2737 adaptiveOrder2737 adaptiveSpanNumericCheck2737_0
        adaptiveSpanEven2737_0 adaptiveSpanWhole2737_0
        adaptiveSpanEvenEntries2737_0 adaptiveSpanWholeEntries2737_0
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanEvenDomain2737_0)
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanWholeDomain2737_0)
  · simpa only [adaptiveSpanLevel2737, adaptiveSpanNumerator2737, adaptiveSpanDenominator2737, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1369) (by decide : 0 < 385)
        adaptiveSpanProfilesValid2737 adaptiveOrder2737 adaptiveSpanNumericCheck2737_1
        adaptiveSpanEven2737_1 adaptiveSpanWhole2737_1
        adaptiveSpanEvenEntries2737_1 adaptiveSpanWholeEntries2737_1
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanEvenDomain2737_1)
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanWholeDomain2737_1)
  · simpa only [adaptiveSpanLevel2737, adaptiveSpanNumerator2737, adaptiveSpanDenominator2737, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1369) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid2737 adaptiveOrder2737 adaptiveSpanNumericCheck2737_2
        adaptiveSpanEven2737_2 adaptiveSpanWhole2737_2
        adaptiveSpanEvenEntries2737_2 adaptiveSpanWholeEntries2737_2
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanEvenDomain2737_2)
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanWholeDomain2737_2)
  · simpa only [adaptiveSpanLevel2737, adaptiveSpanNumerator2737, adaptiveSpanDenominator2737, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1369) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid2737 adaptiveOrder2737 adaptiveSpanNumericCheck2737_3
        adaptiveSpanEven2737_3 adaptiveSpanWhole2737_3
        adaptiveSpanEvenEntries2737_3 adaptiveSpanWholeEntries2737_3
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanEvenDomain2737_3)
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanWholeDomain2737_3)
  · simpa only [adaptiveSpanLevel2737, adaptiveSpanNumerator2737, adaptiveSpanDenominator2737, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1369) (by decide : 0 < 221)
        adaptiveSpanProfilesValid2737 adaptiveOrder2737 adaptiveSpanNumericCheck2737_4
        adaptiveSpanEven2737_4 adaptiveSpanWhole2737_4
        adaptiveSpanEvenEntries2737_4 adaptiveSpanWholeEntries2737_4
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanEvenDomain2737_4)
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanWholeDomain2737_4)
  · simpa only [adaptiveSpanLevel2737, adaptiveSpanNumerator2737, adaptiveSpanDenominator2737, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1369) (by decide : 0 < 323)
        adaptiveSpanProfilesValid2737 adaptiveOrder2737 adaptiveSpanNumericCheck2737_5
        adaptiveSpanEven2737_5 adaptiveSpanWhole2737_5
        adaptiveSpanEvenEntries2737_5 adaptiveSpanWholeEntries2737_5
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanEvenDomain2737_5)
        (by rw [adaptiveSpanProfileLength2737]; exact adaptiveSpanWholeDomain2737_5)

/-- The complete finite histogram certificate for 2671 ≤ n ≤ 2737. -/
theorem adaptiveSpanHistogram2737 : DegreeIntervalCertificate 2737 adaptiveSpanPrimes2737
    (fun s v => sharpDegree (2671 / 2) 7 (adaptiveSpanNumerator2737 s)
      (adaptiveSpanDenominator2737 s) (totientDensity v))
    (fun s v => sharpDegree 2671 7 (adaptiveSpanNumerator2737 s)
      (adaptiveSpanDenominator2737 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows2737)
    adaptiveSpanPrimes2737
    (fun s => sharpDegree (2671 / 2) 7 (adaptiveSpanNumerator2737 s) (adaptiveSpanDenominator2737 s))
    (fun s => sharpDegree 2671 7 (adaptiveSpanNumerator2737 s) (adaptiveSpanDenominator2737 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid2737 adaptiveOrder2737 (coreOrderPermutationCheck_sound adaptivePermutation2737)
    (by rw [adaptiveSpanProfileLength2737]; decide +kernel)
    adaptiveSpanLevel2737 adaptiveSpanTreeCache2737 adaptiveSpanTreeRepresents2737
    (fun j => adaptiveSpanWitness2737.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck2737

/-- Every required odd cycle for a dense set, throughout 2671 ≤ n ≤ 2737. -/
theorem adaptiveSpanInterval2737 {n : ℕ} (hLn : 2671 ≤ n) (hnU : n ≤ 2737)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes2737
    adaptiveSpanNumerator2737 adaptiveSpanDenominator2737 adaptiveSpanSharpTail2737
    adaptiveSpanPrimeSupport2737 adaptiveSpanHistogram2737 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail2737
#print axioms adaptiveSpanPrimeSupport2737
#print axioms adaptiveSpanHistogram2737
#print axioms adaptiveSpanInterval2737
end Erdos883Verified
