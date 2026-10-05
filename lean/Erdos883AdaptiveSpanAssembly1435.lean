import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1435Metadata
import Erdos883AdaptiveSpan1435Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1435 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1435 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1435 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1435 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1435.length) :
    SharpTailCertificate 1435 (adaptiveSpanPrimes1435.take s)
      (adaptiveSpanNumerator1435 s) (adaptiveSpanDenominator1435 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1435 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1435 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1435 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1435 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1435 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1435 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1435 : ∀ u ∈ oddUniverse 1435,
    ∀ v ∈ oddUniverse 1435, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1435 : AdaptiveProfileRowsValid adaptiveRows1435 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1435

theorem adaptiveSpanProfileLength1435 : adaptiveRows1435.length = halfOdds 1435 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1435)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1435 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1435.length) :
    (adaptiveSpanLevel1435 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1435 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1435, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1435_0 adaptiveSpanWholeCache1435_0
  · simpa only [adaptiveSpanLevel1435, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1435_1 adaptiveSpanWholeCache1435_1
  · simpa only [adaptiveSpanLevel1435, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1435_2 adaptiveSpanWholeCache1435_2
  · simpa only [adaptiveSpanLevel1435, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1435_3 adaptiveSpanWholeCache1435_3
  · simpa only [adaptiveSpanLevel1435, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1435_4 adaptiveSpanWholeCache1435_4
  · simpa only [adaptiveSpanLevel1435, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1435_5 adaptiveSpanWholeCache1435_5

theorem adaptiveSpanTreeRepresents1435 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1435.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1435 (halfOdds 1435)
      (sharpDegree (1400 / 2) 6 (adaptiveSpanNumerator1435 s) (adaptiveSpanDenominator1435 s))
      (sharpDegree 1400 6 (adaptiveSpanNumerator1435 s) (adaptiveSpanDenominator1435 s))
      (adaptiveSpanLevel1435 s).1 (adaptiveSpanLevel1435 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1435, adaptiveSpanNumerator1435, adaptiveSpanDenominator1435, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 718) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1435 adaptiveOrder1435 adaptiveSpanNumericCheck1435_0
        adaptiveSpanEven1435_0 adaptiveSpanWhole1435_0
        adaptiveSpanEvenEntries1435_0 adaptiveSpanWholeEntries1435_0
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanEvenDomain1435_0)
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanWholeDomain1435_0)
  · simpa only [adaptiveSpanLevel1435, adaptiveSpanNumerator1435, adaptiveSpanDenominator1435, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 718) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1435 adaptiveOrder1435 adaptiveSpanNumericCheck1435_1
        adaptiveSpanEven1435_1 adaptiveSpanWhole1435_1
        adaptiveSpanEvenEntries1435_1 adaptiveSpanWholeEntries1435_1
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanEvenDomain1435_1)
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanWholeDomain1435_1)
  · simpa only [adaptiveSpanLevel1435, adaptiveSpanNumerator1435, adaptiveSpanDenominator1435, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 718) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1435 adaptiveOrder1435 adaptiveSpanNumericCheck1435_2
        adaptiveSpanEven1435_2 adaptiveSpanWhole1435_2
        adaptiveSpanEvenEntries1435_2 adaptiveSpanWholeEntries1435_2
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanEvenDomain1435_2)
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanWholeDomain1435_2)
  · simpa only [adaptiveSpanLevel1435, adaptiveSpanNumerator1435, adaptiveSpanDenominator1435, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 718) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1435 adaptiveOrder1435 adaptiveSpanNumericCheck1435_3
        adaptiveSpanEven1435_3 adaptiveSpanWhole1435_3
        adaptiveSpanEvenEntries1435_3 adaptiveSpanWholeEntries1435_3
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanEvenDomain1435_3)
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanWholeDomain1435_3)
  · simpa only [adaptiveSpanLevel1435, adaptiveSpanNumerator1435, adaptiveSpanDenominator1435, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 718) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1435 adaptiveOrder1435 adaptiveSpanNumericCheck1435_4
        adaptiveSpanEven1435_4 adaptiveSpanWhole1435_4
        adaptiveSpanEvenEntries1435_4 adaptiveSpanWholeEntries1435_4
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanEvenDomain1435_4)
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanWholeDomain1435_4)
  · simpa only [adaptiveSpanLevel1435, adaptiveSpanNumerator1435, adaptiveSpanDenominator1435, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 718) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1435 adaptiveOrder1435 adaptiveSpanNumericCheck1435_5
        adaptiveSpanEven1435_5 adaptiveSpanWhole1435_5
        adaptiveSpanEvenEntries1435_5 adaptiveSpanWholeEntries1435_5
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanEvenDomain1435_5)
        (by rw [adaptiveSpanProfileLength1435]; exact adaptiveSpanWholeDomain1435_5)

/-- The complete finite histogram certificate for 1400 ≤ n ≤ 1435. -/
theorem adaptiveSpanHistogram1435 : DegreeIntervalCertificate 1435 adaptiveSpanPrimes1435
    (fun s v => sharpDegree (1400 / 2) 6 (adaptiveSpanNumerator1435 s)
      (adaptiveSpanDenominator1435 s) (totientDensity v))
    (fun s v => sharpDegree 1400 6 (adaptiveSpanNumerator1435 s)
      (adaptiveSpanDenominator1435 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1435)
    adaptiveSpanPrimes1435
    (fun s => sharpDegree (1400 / 2) 6 (adaptiveSpanNumerator1435 s) (adaptiveSpanDenominator1435 s))
    (fun s => sharpDegree 1400 6 (adaptiveSpanNumerator1435 s) (adaptiveSpanDenominator1435 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1435 adaptiveOrder1435 (coreOrderPermutationCheck_sound adaptivePermutation1435)
    (by rw [adaptiveSpanProfileLength1435]; decide +kernel)
    adaptiveSpanLevel1435 adaptiveSpanTreeCache1435 adaptiveSpanTreeRepresents1435
    (fun j => adaptiveSpanWitness1435.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1435

/-- Every required odd cycle for a dense set, throughout 1400 ≤ n ≤ 1435. -/
theorem adaptiveSpanInterval1435 {n : ℕ} (hLn : 1400 ≤ n) (hnU : n ≤ 1435)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1435
    adaptiveSpanNumerator1435 adaptiveSpanDenominator1435 adaptiveSpanSharpTail1435
    adaptiveSpanPrimeSupport1435 adaptiveSpanHistogram1435 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1435
#print axioms adaptiveSpanPrimeSupport1435
#print axioms adaptiveSpanHistogram1435
#print axioms adaptiveSpanInterval1435
end Erdos883Verified
