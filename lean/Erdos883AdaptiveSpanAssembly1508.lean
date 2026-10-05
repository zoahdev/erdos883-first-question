import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1508Metadata
import Erdos883AdaptiveSpan1508Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1508 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1508 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1508 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1508 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1508.length) :
    SharpTailCertificate 1508 (adaptiveSpanPrimes1508.take s)
      (adaptiveSpanNumerator1508 s) (adaptiveSpanDenominator1508 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1508 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1508 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1508 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1508 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1508 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1508 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1508 : ∀ u ∈ oddUniverse 1508,
    ∀ v ∈ oddUniverse 1508, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1508 : AdaptiveProfileRowsValid adaptiveRows1508 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1508

theorem adaptiveSpanProfileLength1508 : adaptiveRows1508.length = halfOdds 1508 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1508)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1508 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1508.length) :
    (adaptiveSpanLevel1508 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1508 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1508, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1508_0 adaptiveSpanWholeCache1508_0
  · simpa only [adaptiveSpanLevel1508, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1508_1 adaptiveSpanWholeCache1508_1
  · simpa only [adaptiveSpanLevel1508, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1508_2 adaptiveSpanWholeCache1508_2
  · simpa only [adaptiveSpanLevel1508, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1508_3 adaptiveSpanWholeCache1508_3
  · simpa only [adaptiveSpanLevel1508, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1508_4 adaptiveSpanWholeCache1508_4
  · simpa only [adaptiveSpanLevel1508, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1508_5 adaptiveSpanWholeCache1508_5

theorem adaptiveSpanTreeRepresents1508 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1508.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1508 (halfOdds 1508)
      (sharpDegree (1472 / 2) 6 (adaptiveSpanNumerator1508 s) (adaptiveSpanDenominator1508 s))
      (sharpDegree 1472 6 (adaptiveSpanNumerator1508 s) (adaptiveSpanDenominator1508 s))
      (adaptiveSpanLevel1508 s).1 (adaptiveSpanLevel1508 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1508, adaptiveSpanNumerator1508, adaptiveSpanDenominator1508, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 754) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1508 adaptiveOrder1508 adaptiveSpanNumericCheck1508_0
        adaptiveSpanEven1508_0 adaptiveSpanWhole1508_0
        adaptiveSpanEvenEntries1508_0 adaptiveSpanWholeEntries1508_0
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanEvenDomain1508_0)
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanWholeDomain1508_0)
  · simpa only [adaptiveSpanLevel1508, adaptiveSpanNumerator1508, adaptiveSpanDenominator1508, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 754) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1508 adaptiveOrder1508 adaptiveSpanNumericCheck1508_1
        adaptiveSpanEven1508_1 adaptiveSpanWhole1508_1
        adaptiveSpanEvenEntries1508_1 adaptiveSpanWholeEntries1508_1
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanEvenDomain1508_1)
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanWholeDomain1508_1)
  · simpa only [adaptiveSpanLevel1508, adaptiveSpanNumerator1508, adaptiveSpanDenominator1508, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 754) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1508 adaptiveOrder1508 adaptiveSpanNumericCheck1508_2
        adaptiveSpanEven1508_2 adaptiveSpanWhole1508_2
        adaptiveSpanEvenEntries1508_2 adaptiveSpanWholeEntries1508_2
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanEvenDomain1508_2)
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanWholeDomain1508_2)
  · simpa only [adaptiveSpanLevel1508, adaptiveSpanNumerator1508, adaptiveSpanDenominator1508, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 754) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1508 adaptiveOrder1508 adaptiveSpanNumericCheck1508_3
        adaptiveSpanEven1508_3 adaptiveSpanWhole1508_3
        adaptiveSpanEvenEntries1508_3 adaptiveSpanWholeEntries1508_3
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanEvenDomain1508_3)
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanWholeDomain1508_3)
  · simpa only [adaptiveSpanLevel1508, adaptiveSpanNumerator1508, adaptiveSpanDenominator1508, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 754) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1508 adaptiveOrder1508 adaptiveSpanNumericCheck1508_4
        adaptiveSpanEven1508_4 adaptiveSpanWhole1508_4
        adaptiveSpanEvenEntries1508_4 adaptiveSpanWholeEntries1508_4
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanEvenDomain1508_4)
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanWholeDomain1508_4)
  · simpa only [adaptiveSpanLevel1508, adaptiveSpanNumerator1508, adaptiveSpanDenominator1508, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 754) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1508 adaptiveOrder1508 adaptiveSpanNumericCheck1508_5
        adaptiveSpanEven1508_5 adaptiveSpanWhole1508_5
        adaptiveSpanEvenEntries1508_5 adaptiveSpanWholeEntries1508_5
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanEvenDomain1508_5)
        (by rw [adaptiveSpanProfileLength1508]; exact adaptiveSpanWholeDomain1508_5)

/-- The complete finite histogram certificate for 1472 ≤ n ≤ 1508. -/
theorem adaptiveSpanHistogram1508 : DegreeIntervalCertificate 1508 adaptiveSpanPrimes1508
    (fun s v => sharpDegree (1472 / 2) 6 (adaptiveSpanNumerator1508 s)
      (adaptiveSpanDenominator1508 s) (totientDensity v))
    (fun s v => sharpDegree 1472 6 (adaptiveSpanNumerator1508 s)
      (adaptiveSpanDenominator1508 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1508)
    adaptiveSpanPrimes1508
    (fun s => sharpDegree (1472 / 2) 6 (adaptiveSpanNumerator1508 s) (adaptiveSpanDenominator1508 s))
    (fun s => sharpDegree 1472 6 (adaptiveSpanNumerator1508 s) (adaptiveSpanDenominator1508 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1508 adaptiveOrder1508 (coreOrderPermutationCheck_sound adaptivePermutation1508)
    (by rw [adaptiveSpanProfileLength1508]; decide +kernel)
    adaptiveSpanLevel1508 adaptiveSpanTreeCache1508 adaptiveSpanTreeRepresents1508
    (fun j => adaptiveSpanWitness1508.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1508

/-- Every required odd cycle for a dense set, throughout 1472 ≤ n ≤ 1508. -/
theorem adaptiveSpanInterval1508 {n : ℕ} (hLn : 1472 ≤ n) (hnU : n ≤ 1508)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1508
    adaptiveSpanNumerator1508 adaptiveSpanDenominator1508 adaptiveSpanSharpTail1508
    adaptiveSpanPrimeSupport1508 adaptiveSpanHistogram1508 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1508
#print axioms adaptiveSpanPrimeSupport1508
#print axioms adaptiveSpanHistogram1508
#print axioms adaptiveSpanInterval1508
end Erdos883Verified
