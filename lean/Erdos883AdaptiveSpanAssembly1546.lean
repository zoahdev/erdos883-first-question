import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1546Metadata
import Erdos883AdaptiveSpan1546Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1546 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1546 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1546 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1546 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1546.length) :
    SharpTailCertificate 1546 (adaptiveSpanPrimes1546.take s)
      (adaptiveSpanNumerator1546 s) (adaptiveSpanDenominator1546 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1546 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1546 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1546 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1546 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1546 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1546 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1546 : ∀ u ∈ oddUniverse 1546,
    ∀ v ∈ oddUniverse 1546, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1546 : AdaptiveProfileRowsValid adaptiveRows1546 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1546

theorem adaptiveSpanProfileLength1546 : adaptiveRows1546.length = halfOdds 1546 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1546)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1546 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1546.length) :
    (adaptiveSpanLevel1546 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1546 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1546, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1546_0 adaptiveSpanWholeCache1546_0
  · simpa only [adaptiveSpanLevel1546, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1546_1 adaptiveSpanWholeCache1546_1
  · simpa only [adaptiveSpanLevel1546, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1546_2 adaptiveSpanWholeCache1546_2
  · simpa only [adaptiveSpanLevel1546, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1546_3 adaptiveSpanWholeCache1546_3
  · simpa only [adaptiveSpanLevel1546, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1546_4 adaptiveSpanWholeCache1546_4
  · simpa only [adaptiveSpanLevel1546, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1546_5 adaptiveSpanWholeCache1546_5

theorem adaptiveSpanTreeRepresents1546 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1546.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1546 (halfOdds 1546)
      (sharpDegree (1509 / 2) 6 (adaptiveSpanNumerator1546 s) (adaptiveSpanDenominator1546 s))
      (sharpDegree 1509 6 (adaptiveSpanNumerator1546 s) (adaptiveSpanDenominator1546 s))
      (adaptiveSpanLevel1546 s).1 (adaptiveSpanLevel1546 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1546, adaptiveSpanNumerator1546, adaptiveSpanDenominator1546, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 773) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1546 adaptiveOrder1546 adaptiveSpanNumericCheck1546_0
        adaptiveSpanEven1546_0 adaptiveSpanWhole1546_0
        adaptiveSpanEvenEntries1546_0 adaptiveSpanWholeEntries1546_0
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanEvenDomain1546_0)
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanWholeDomain1546_0)
  · simpa only [adaptiveSpanLevel1546, adaptiveSpanNumerator1546, adaptiveSpanDenominator1546, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 773) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1546 adaptiveOrder1546 adaptiveSpanNumericCheck1546_1
        adaptiveSpanEven1546_1 adaptiveSpanWhole1546_1
        adaptiveSpanEvenEntries1546_1 adaptiveSpanWholeEntries1546_1
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanEvenDomain1546_1)
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanWholeDomain1546_1)
  · simpa only [adaptiveSpanLevel1546, adaptiveSpanNumerator1546, adaptiveSpanDenominator1546, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 773) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1546 adaptiveOrder1546 adaptiveSpanNumericCheck1546_2
        adaptiveSpanEven1546_2 adaptiveSpanWhole1546_2
        adaptiveSpanEvenEntries1546_2 adaptiveSpanWholeEntries1546_2
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanEvenDomain1546_2)
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanWholeDomain1546_2)
  · simpa only [adaptiveSpanLevel1546, adaptiveSpanNumerator1546, adaptiveSpanDenominator1546, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 773) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1546 adaptiveOrder1546 adaptiveSpanNumericCheck1546_3
        adaptiveSpanEven1546_3 adaptiveSpanWhole1546_3
        adaptiveSpanEvenEntries1546_3 adaptiveSpanWholeEntries1546_3
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanEvenDomain1546_3)
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanWholeDomain1546_3)
  · simpa only [adaptiveSpanLevel1546, adaptiveSpanNumerator1546, adaptiveSpanDenominator1546, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 773) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1546 adaptiveOrder1546 adaptiveSpanNumericCheck1546_4
        adaptiveSpanEven1546_4 adaptiveSpanWhole1546_4
        adaptiveSpanEvenEntries1546_4 adaptiveSpanWholeEntries1546_4
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanEvenDomain1546_4)
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanWholeDomain1546_4)
  · simpa only [adaptiveSpanLevel1546, adaptiveSpanNumerator1546, adaptiveSpanDenominator1546, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 773) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1546 adaptiveOrder1546 adaptiveSpanNumericCheck1546_5
        adaptiveSpanEven1546_5 adaptiveSpanWhole1546_5
        adaptiveSpanEvenEntries1546_5 adaptiveSpanWholeEntries1546_5
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanEvenDomain1546_5)
        (by rw [adaptiveSpanProfileLength1546]; exact adaptiveSpanWholeDomain1546_5)

/-- The complete finite histogram certificate for 1509 ≤ n ≤ 1546. -/
theorem adaptiveSpanHistogram1546 : DegreeIntervalCertificate 1546 adaptiveSpanPrimes1546
    (fun s v => sharpDegree (1509 / 2) 6 (adaptiveSpanNumerator1546 s)
      (adaptiveSpanDenominator1546 s) (totientDensity v))
    (fun s v => sharpDegree 1509 6 (adaptiveSpanNumerator1546 s)
      (adaptiveSpanDenominator1546 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1546)
    adaptiveSpanPrimes1546
    (fun s => sharpDegree (1509 / 2) 6 (adaptiveSpanNumerator1546 s) (adaptiveSpanDenominator1546 s))
    (fun s => sharpDegree 1509 6 (adaptiveSpanNumerator1546 s) (adaptiveSpanDenominator1546 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1546 adaptiveOrder1546 (coreOrderPermutationCheck_sound adaptivePermutation1546)
    (by rw [adaptiveSpanProfileLength1546]; decide +kernel)
    adaptiveSpanLevel1546 adaptiveSpanTreeCache1546 adaptiveSpanTreeRepresents1546
    (fun j => adaptiveSpanWitness1546.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1546

/-- Every required odd cycle for a dense set, throughout 1509 ≤ n ≤ 1546. -/
theorem adaptiveSpanInterval1546 {n : ℕ} (hLn : 1509 ≤ n) (hnU : n ≤ 1546)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1546
    adaptiveSpanNumerator1546 adaptiveSpanDenominator1546 adaptiveSpanSharpTail1546
    adaptiveSpanPrimeSupport1546 adaptiveSpanHistogram1546 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1546
#print axioms adaptiveSpanPrimeSupport1546
#print axioms adaptiveSpanHistogram1546
#print axioms adaptiveSpanInterval1546
end Erdos883Verified
