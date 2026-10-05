import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1708Metadata
import Erdos883AdaptiveSpan1708Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1708 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1708 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1708 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1708 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1708.length) :
    SharpTailCertificate 1708 (adaptiveSpanPrimes1708.take s)
      (adaptiveSpanNumerator1708 s) (adaptiveSpanDenominator1708 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1708 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1708 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1708 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1708 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1708 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1708 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1708 : ∀ u ∈ oddUniverse 1708,
    ∀ v ∈ oddUniverse 1708, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1708 : AdaptiveProfileRowsValid adaptiveRows1708 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1708

theorem adaptiveSpanProfileLength1708 : adaptiveRows1708.length = halfOdds 1708 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1708)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1708 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1708.length) :
    (adaptiveSpanLevel1708 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1708 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1708, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1708_0 adaptiveSpanWholeCache1708_0
  · simpa only [adaptiveSpanLevel1708, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1708_1 adaptiveSpanWholeCache1708_1
  · simpa only [adaptiveSpanLevel1708, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1708_2 adaptiveSpanWholeCache1708_2
  · simpa only [adaptiveSpanLevel1708, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1708_3 adaptiveSpanWholeCache1708_3
  · simpa only [adaptiveSpanLevel1708, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1708_4 adaptiveSpanWholeCache1708_4
  · simpa only [adaptiveSpanLevel1708, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1708_5 adaptiveSpanWholeCache1708_5

theorem adaptiveSpanTreeRepresents1708 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1708.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1708 (halfOdds 1708)
      (sharpDegree (1667 / 2) 6 (adaptiveSpanNumerator1708 s) (adaptiveSpanDenominator1708 s))
      (sharpDegree 1667 6 (adaptiveSpanNumerator1708 s) (adaptiveSpanDenominator1708 s))
      (adaptiveSpanLevel1708 s).1 (adaptiveSpanLevel1708 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1708, adaptiveSpanNumerator1708, adaptiveSpanDenominator1708, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 854) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1708 adaptiveOrder1708 adaptiveSpanNumericCheck1708_0
        adaptiveSpanEven1708_0 adaptiveSpanWhole1708_0
        adaptiveSpanEvenEntries1708_0 adaptiveSpanWholeEntries1708_0
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanEvenDomain1708_0)
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanWholeDomain1708_0)
  · simpa only [adaptiveSpanLevel1708, adaptiveSpanNumerator1708, adaptiveSpanDenominator1708, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 854) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1708 adaptiveOrder1708 adaptiveSpanNumericCheck1708_1
        adaptiveSpanEven1708_1 adaptiveSpanWhole1708_1
        adaptiveSpanEvenEntries1708_1 adaptiveSpanWholeEntries1708_1
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanEvenDomain1708_1)
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanWholeDomain1708_1)
  · simpa only [adaptiveSpanLevel1708, adaptiveSpanNumerator1708, adaptiveSpanDenominator1708, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 854) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1708 adaptiveOrder1708 adaptiveSpanNumericCheck1708_2
        adaptiveSpanEven1708_2 adaptiveSpanWhole1708_2
        adaptiveSpanEvenEntries1708_2 adaptiveSpanWholeEntries1708_2
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanEvenDomain1708_2)
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanWholeDomain1708_2)
  · simpa only [adaptiveSpanLevel1708, adaptiveSpanNumerator1708, adaptiveSpanDenominator1708, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 854) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1708 adaptiveOrder1708 adaptiveSpanNumericCheck1708_3
        adaptiveSpanEven1708_3 adaptiveSpanWhole1708_3
        adaptiveSpanEvenEntries1708_3 adaptiveSpanWholeEntries1708_3
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanEvenDomain1708_3)
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanWholeDomain1708_3)
  · simpa only [adaptiveSpanLevel1708, adaptiveSpanNumerator1708, adaptiveSpanDenominator1708, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 854) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1708 adaptiveOrder1708 adaptiveSpanNumericCheck1708_4
        adaptiveSpanEven1708_4 adaptiveSpanWhole1708_4
        adaptiveSpanEvenEntries1708_4 adaptiveSpanWholeEntries1708_4
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanEvenDomain1708_4)
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanWholeDomain1708_4)
  · simpa only [adaptiveSpanLevel1708, adaptiveSpanNumerator1708, adaptiveSpanDenominator1708, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 854) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1708 adaptiveOrder1708 adaptiveSpanNumericCheck1708_5
        adaptiveSpanEven1708_5 adaptiveSpanWhole1708_5
        adaptiveSpanEvenEntries1708_5 adaptiveSpanWholeEntries1708_5
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanEvenDomain1708_5)
        (by rw [adaptiveSpanProfileLength1708]; exact adaptiveSpanWholeDomain1708_5)

/-- The complete finite histogram certificate for 1667 ≤ n ≤ 1708. -/
theorem adaptiveSpanHistogram1708 : DegreeIntervalCertificate 1708 adaptiveSpanPrimes1708
    (fun s v => sharpDegree (1667 / 2) 6 (adaptiveSpanNumerator1708 s)
      (adaptiveSpanDenominator1708 s) (totientDensity v))
    (fun s v => sharpDegree 1667 6 (adaptiveSpanNumerator1708 s)
      (adaptiveSpanDenominator1708 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1708)
    adaptiveSpanPrimes1708
    (fun s => sharpDegree (1667 / 2) 6 (adaptiveSpanNumerator1708 s) (adaptiveSpanDenominator1708 s))
    (fun s => sharpDegree 1667 6 (adaptiveSpanNumerator1708 s) (adaptiveSpanDenominator1708 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1708 adaptiveOrder1708 (coreOrderPermutationCheck_sound adaptivePermutation1708)
    (by rw [adaptiveSpanProfileLength1708]; decide +kernel)
    adaptiveSpanLevel1708 adaptiveSpanTreeCache1708 adaptiveSpanTreeRepresents1708
    (fun j => adaptiveSpanWitness1708.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1708

/-- Every required odd cycle for a dense set, throughout 1667 ≤ n ≤ 1708. -/
theorem adaptiveSpanInterval1708 {n : ℕ} (hLn : 1667 ≤ n) (hnU : n ≤ 1708)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1708
    adaptiveSpanNumerator1708 adaptiveSpanDenominator1708 adaptiveSpanSharpTail1708
    adaptiveSpanPrimeSupport1708 adaptiveSpanHistogram1708 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1708
#print axioms adaptiveSpanPrimeSupport1708
#print axioms adaptiveSpanHistogram1708
#print axioms adaptiveSpanInterval1708
end Erdos883Verified
