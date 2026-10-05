import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1399Metadata
import Erdos883AdaptiveSpan1399Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1399 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1399 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1399 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1399 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1399.length) :
    SharpTailCertificate 1399 (adaptiveSpanPrimes1399.take s)
      (adaptiveSpanNumerator1399 s) (adaptiveSpanDenominator1399 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1399 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1399 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1399 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1399 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1399 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1399 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1399 : ∀ u ∈ oddUniverse 1399,
    ∀ v ∈ oddUniverse 1399, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1399 : AdaptiveProfileRowsValid adaptiveRows1399 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1399

theorem adaptiveSpanProfileLength1399 : adaptiveRows1399.length = halfOdds 1399 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1399)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1399 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1399.length) :
    (adaptiveSpanLevel1399 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1399 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1399, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1399_0 adaptiveSpanWholeCache1399_0
  · simpa only [adaptiveSpanLevel1399, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1399_1 adaptiveSpanWholeCache1399_1
  · simpa only [adaptiveSpanLevel1399, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1399_2 adaptiveSpanWholeCache1399_2
  · simpa only [adaptiveSpanLevel1399, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1399_3 adaptiveSpanWholeCache1399_3
  · simpa only [adaptiveSpanLevel1399, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1399_4 adaptiveSpanWholeCache1399_4
  · simpa only [adaptiveSpanLevel1399, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1399_5 adaptiveSpanWholeCache1399_5

theorem adaptiveSpanTreeRepresents1399 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1399.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1399 (halfOdds 1399)
      (sharpDegree (1365 / 2) 6 (adaptiveSpanNumerator1399 s) (adaptiveSpanDenominator1399 s))
      (sharpDegree 1365 6 (adaptiveSpanNumerator1399 s) (adaptiveSpanDenominator1399 s))
      (adaptiveSpanLevel1399 s).1 (adaptiveSpanLevel1399 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1399, adaptiveSpanNumerator1399, adaptiveSpanDenominator1399, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 700) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1399 adaptiveOrder1399 adaptiveSpanNumericCheck1399_0
        adaptiveSpanEven1399_0 adaptiveSpanWhole1399_0
        adaptiveSpanEvenEntries1399_0 adaptiveSpanWholeEntries1399_0
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanEvenDomain1399_0)
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanWholeDomain1399_0)
  · simpa only [adaptiveSpanLevel1399, adaptiveSpanNumerator1399, adaptiveSpanDenominator1399, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 700) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1399 adaptiveOrder1399 adaptiveSpanNumericCheck1399_1
        adaptiveSpanEven1399_1 adaptiveSpanWhole1399_1
        adaptiveSpanEvenEntries1399_1 adaptiveSpanWholeEntries1399_1
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanEvenDomain1399_1)
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanWholeDomain1399_1)
  · simpa only [adaptiveSpanLevel1399, adaptiveSpanNumerator1399, adaptiveSpanDenominator1399, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 700) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1399 adaptiveOrder1399 adaptiveSpanNumericCheck1399_2
        adaptiveSpanEven1399_2 adaptiveSpanWhole1399_2
        adaptiveSpanEvenEntries1399_2 adaptiveSpanWholeEntries1399_2
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanEvenDomain1399_2)
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanWholeDomain1399_2)
  · simpa only [adaptiveSpanLevel1399, adaptiveSpanNumerator1399, adaptiveSpanDenominator1399, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 700) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1399 adaptiveOrder1399 adaptiveSpanNumericCheck1399_3
        adaptiveSpanEven1399_3 adaptiveSpanWhole1399_3
        adaptiveSpanEvenEntries1399_3 adaptiveSpanWholeEntries1399_3
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanEvenDomain1399_3)
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanWholeDomain1399_3)
  · simpa only [adaptiveSpanLevel1399, adaptiveSpanNumerator1399, adaptiveSpanDenominator1399, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 700) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1399 adaptiveOrder1399 adaptiveSpanNumericCheck1399_4
        adaptiveSpanEven1399_4 adaptiveSpanWhole1399_4
        adaptiveSpanEvenEntries1399_4 adaptiveSpanWholeEntries1399_4
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanEvenDomain1399_4)
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanWholeDomain1399_4)
  · simpa only [adaptiveSpanLevel1399, adaptiveSpanNumerator1399, adaptiveSpanDenominator1399, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 700) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1399 adaptiveOrder1399 adaptiveSpanNumericCheck1399_5
        adaptiveSpanEven1399_5 adaptiveSpanWhole1399_5
        adaptiveSpanEvenEntries1399_5 adaptiveSpanWholeEntries1399_5
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanEvenDomain1399_5)
        (by rw [adaptiveSpanProfileLength1399]; exact adaptiveSpanWholeDomain1399_5)

/-- The complete finite histogram certificate for 1365 ≤ n ≤ 1399. -/
theorem adaptiveSpanHistogram1399 : DegreeIntervalCertificate 1399 adaptiveSpanPrimes1399
    (fun s v => sharpDegree (1365 / 2) 6 (adaptiveSpanNumerator1399 s)
      (adaptiveSpanDenominator1399 s) (totientDensity v))
    (fun s v => sharpDegree 1365 6 (adaptiveSpanNumerator1399 s)
      (adaptiveSpanDenominator1399 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1399)
    adaptiveSpanPrimes1399
    (fun s => sharpDegree (1365 / 2) 6 (adaptiveSpanNumerator1399 s) (adaptiveSpanDenominator1399 s))
    (fun s => sharpDegree 1365 6 (adaptiveSpanNumerator1399 s) (adaptiveSpanDenominator1399 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1399 adaptiveOrder1399 (coreOrderPermutationCheck_sound adaptivePermutation1399)
    (by rw [adaptiveSpanProfileLength1399]; decide +kernel)
    adaptiveSpanLevel1399 adaptiveSpanTreeCache1399 adaptiveSpanTreeRepresents1399
    (fun j => adaptiveSpanWitness1399.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1399

/-- Every required odd cycle for a dense set, throughout 1365 ≤ n ≤ 1399. -/
theorem adaptiveSpanInterval1399 {n : ℕ} (hLn : 1365 ≤ n) (hnU : n ≤ 1399)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1399
    adaptiveSpanNumerator1399 adaptiveSpanDenominator1399 adaptiveSpanSharpTail1399
    adaptiveSpanPrimeSupport1399 adaptiveSpanHistogram1399 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1399
#print axioms adaptiveSpanPrimeSupport1399
#print axioms adaptiveSpanHistogram1399
#print axioms adaptiveSpanInterval1399
end Erdos883Verified
