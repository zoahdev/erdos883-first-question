import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1585Metadata
import Erdos883AdaptiveSpan1585Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1585 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1585 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1585 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1585 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1585.length) :
    SharpTailCertificate 1585 (adaptiveSpanPrimes1585.take s)
      (adaptiveSpanNumerator1585 s) (adaptiveSpanDenominator1585 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1585 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1585 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1585 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1585 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1585 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1585 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1585 : ∀ u ∈ oddUniverse 1585,
    ∀ v ∈ oddUniverse 1585, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1585 : AdaptiveProfileRowsValid adaptiveRows1585 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1585

theorem adaptiveSpanProfileLength1585 : adaptiveRows1585.length = halfOdds 1585 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1585)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1585 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1585.length) :
    (adaptiveSpanLevel1585 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1585 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1585, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1585_0 adaptiveSpanWholeCache1585_0
  · simpa only [adaptiveSpanLevel1585, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1585_1 adaptiveSpanWholeCache1585_1
  · simpa only [adaptiveSpanLevel1585, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1585_2 adaptiveSpanWholeCache1585_2
  · simpa only [adaptiveSpanLevel1585, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1585_3 adaptiveSpanWholeCache1585_3
  · simpa only [adaptiveSpanLevel1585, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1585_4 adaptiveSpanWholeCache1585_4
  · simpa only [adaptiveSpanLevel1585, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1585_5 adaptiveSpanWholeCache1585_5

theorem adaptiveSpanTreeRepresents1585 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1585.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1585 (halfOdds 1585)
      (sharpDegree (1547 / 2) 6 (adaptiveSpanNumerator1585 s) (adaptiveSpanDenominator1585 s))
      (sharpDegree 1547 6 (adaptiveSpanNumerator1585 s) (adaptiveSpanDenominator1585 s))
      (adaptiveSpanLevel1585 s).1 (adaptiveSpanLevel1585 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1585, adaptiveSpanNumerator1585, adaptiveSpanDenominator1585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 793) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1585 adaptiveOrder1585 adaptiveSpanNumericCheck1585_0
        adaptiveSpanEven1585_0 adaptiveSpanWhole1585_0
        adaptiveSpanEvenEntries1585_0 adaptiveSpanWholeEntries1585_0
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanEvenDomain1585_0)
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanWholeDomain1585_0)
  · simpa only [adaptiveSpanLevel1585, adaptiveSpanNumerator1585, adaptiveSpanDenominator1585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 793) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1585 adaptiveOrder1585 adaptiveSpanNumericCheck1585_1
        adaptiveSpanEven1585_1 adaptiveSpanWhole1585_1
        adaptiveSpanEvenEntries1585_1 adaptiveSpanWholeEntries1585_1
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanEvenDomain1585_1)
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanWholeDomain1585_1)
  · simpa only [adaptiveSpanLevel1585, adaptiveSpanNumerator1585, adaptiveSpanDenominator1585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 793) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1585 adaptiveOrder1585 adaptiveSpanNumericCheck1585_2
        adaptiveSpanEven1585_2 adaptiveSpanWhole1585_2
        adaptiveSpanEvenEntries1585_2 adaptiveSpanWholeEntries1585_2
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanEvenDomain1585_2)
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanWholeDomain1585_2)
  · simpa only [adaptiveSpanLevel1585, adaptiveSpanNumerator1585, adaptiveSpanDenominator1585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 793) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1585 adaptiveOrder1585 adaptiveSpanNumericCheck1585_3
        adaptiveSpanEven1585_3 adaptiveSpanWhole1585_3
        adaptiveSpanEvenEntries1585_3 adaptiveSpanWholeEntries1585_3
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanEvenDomain1585_3)
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanWholeDomain1585_3)
  · simpa only [adaptiveSpanLevel1585, adaptiveSpanNumerator1585, adaptiveSpanDenominator1585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 793) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1585 adaptiveOrder1585 adaptiveSpanNumericCheck1585_4
        adaptiveSpanEven1585_4 adaptiveSpanWhole1585_4
        adaptiveSpanEvenEntries1585_4 adaptiveSpanWholeEntries1585_4
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanEvenDomain1585_4)
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanWholeDomain1585_4)
  · simpa only [adaptiveSpanLevel1585, adaptiveSpanNumerator1585, adaptiveSpanDenominator1585, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 793) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1585 adaptiveOrder1585 adaptiveSpanNumericCheck1585_5
        adaptiveSpanEven1585_5 adaptiveSpanWhole1585_5
        adaptiveSpanEvenEntries1585_5 adaptiveSpanWholeEntries1585_5
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanEvenDomain1585_5)
        (by rw [adaptiveSpanProfileLength1585]; exact adaptiveSpanWholeDomain1585_5)

/-- The complete finite histogram certificate for 1547 ≤ n ≤ 1585. -/
theorem adaptiveSpanHistogram1585 : DegreeIntervalCertificate 1585 adaptiveSpanPrimes1585
    (fun s v => sharpDegree (1547 / 2) 6 (adaptiveSpanNumerator1585 s)
      (adaptiveSpanDenominator1585 s) (totientDensity v))
    (fun s v => sharpDegree 1547 6 (adaptiveSpanNumerator1585 s)
      (adaptiveSpanDenominator1585 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1585)
    adaptiveSpanPrimes1585
    (fun s => sharpDegree (1547 / 2) 6 (adaptiveSpanNumerator1585 s) (adaptiveSpanDenominator1585 s))
    (fun s => sharpDegree 1547 6 (adaptiveSpanNumerator1585 s) (adaptiveSpanDenominator1585 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1585 adaptiveOrder1585 (coreOrderPermutationCheck_sound adaptivePermutation1585)
    (by rw [adaptiveSpanProfileLength1585]; decide +kernel)
    adaptiveSpanLevel1585 adaptiveSpanTreeCache1585 adaptiveSpanTreeRepresents1585
    (fun j => adaptiveSpanWitness1585.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1585

/-- Every required odd cycle for a dense set, throughout 1547 ≤ n ≤ 1585. -/
theorem adaptiveSpanInterval1585 {n : ℕ} (hLn : 1547 ≤ n) (hnU : n ≤ 1585)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1585
    adaptiveSpanNumerator1585 adaptiveSpanDenominator1585 adaptiveSpanSharpTail1585
    adaptiveSpanPrimeSupport1585 adaptiveSpanHistogram1585 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1585
#print axioms adaptiveSpanPrimeSupport1585
#print axioms adaptiveSpanHistogram1585
#print axioms adaptiveSpanInterval1585
end Erdos883Verified
