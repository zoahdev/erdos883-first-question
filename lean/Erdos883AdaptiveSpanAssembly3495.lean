import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate3495Metadata
import Erdos883AdaptiveSpan3495Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes3495 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator3495 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator3495 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail3495 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3495.length) :
    SharpTailCertificate 3495 (adaptiveSpanPrimes3495.take s)
      (adaptiveSpanNumerator3495 s) (adaptiveSpanDenominator3495 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 3495 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3495 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3495 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3495 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3495 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3495 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3495 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport3495 : ∀ u ∈ oddUniverse 3495,
    ∀ v ∈ oddUniverse 3495, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid3495 : AdaptiveProfileRowsValid adaptiveRows3495 :=
  coreProfileMetadataCheck_sound adaptiveMetadata3495

theorem adaptiveSpanProfileLength3495 : adaptiveRows3495.length = halfOdds 3495 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation3495)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache3495 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3495.length) :
    (adaptiveSpanLevel3495 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel3495 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3495, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3495_0 adaptiveSpanWholeCache3495_0
  · simpa only [adaptiveSpanLevel3495, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3495_1 adaptiveSpanWholeCache3495_1
  · simpa only [adaptiveSpanLevel3495, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3495_2 adaptiveSpanWholeCache3495_2
  · simpa only [adaptiveSpanLevel3495, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3495_3 adaptiveSpanWholeCache3495_3
  · simpa only [adaptiveSpanLevel3495, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3495_4 adaptiveSpanWholeCache3495_4
  · simpa only [adaptiveSpanLevel3495, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3495_5 adaptiveSpanWholeCache3495_5
  · simpa only [adaptiveSpanLevel3495, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3495_6 adaptiveSpanWholeCache3495_6

theorem adaptiveSpanTreeRepresents3495 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3495.length) :
    AdaptiveSpanTreeRepresents adaptiveRows3495 (halfOdds 3495)
      (sharpDegree (3329 / 2) 7 (adaptiveSpanNumerator3495 s) (adaptiveSpanDenominator3495 s))
      (sharpDegree 3329 7 (adaptiveSpanNumerator3495 s) (adaptiveSpanDenominator3495 s))
      (adaptiveSpanLevel3495 s).1 (adaptiveSpanLevel3495 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3495, adaptiveSpanNumerator3495, adaptiveSpanDenominator3495, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1748) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid3495 adaptiveOrder3495 adaptiveSpanNumericCheck3495_0
        adaptiveSpanEven3495_0 adaptiveSpanWhole3495_0
        adaptiveSpanEvenEntries3495_0 adaptiveSpanWholeEntries3495_0
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanEvenDomain3495_0)
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanWholeDomain3495_0)
  · simpa only [adaptiveSpanLevel3495, adaptiveSpanNumerator3495, adaptiveSpanDenominator3495, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1748) (by decide : 0 < 385)
        adaptiveSpanProfilesValid3495 adaptiveOrder3495 adaptiveSpanNumericCheck3495_1
        adaptiveSpanEven3495_1 adaptiveSpanWhole3495_1
        adaptiveSpanEvenEntries3495_1 adaptiveSpanWholeEntries3495_1
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanEvenDomain3495_1)
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanWholeDomain3495_1)
  · simpa only [adaptiveSpanLevel3495, adaptiveSpanNumerator3495, adaptiveSpanDenominator3495, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1748) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid3495 adaptiveOrder3495 adaptiveSpanNumericCheck3495_2
        adaptiveSpanEven3495_2 adaptiveSpanWhole3495_2
        adaptiveSpanEvenEntries3495_2 adaptiveSpanWholeEntries3495_2
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanEvenDomain3495_2)
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanWholeDomain3495_2)
  · simpa only [adaptiveSpanLevel3495, adaptiveSpanNumerator3495, adaptiveSpanDenominator3495, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1748) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid3495 adaptiveOrder3495 adaptiveSpanNumericCheck3495_3
        adaptiveSpanEven3495_3 adaptiveSpanWhole3495_3
        adaptiveSpanEvenEntries3495_3 adaptiveSpanWholeEntries3495_3
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanEvenDomain3495_3)
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanWholeDomain3495_3)
  · simpa only [adaptiveSpanLevel3495, adaptiveSpanNumerator3495, adaptiveSpanDenominator3495, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1748) (by decide : 0 < 221)
        adaptiveSpanProfilesValid3495 adaptiveOrder3495 adaptiveSpanNumericCheck3495_4
        adaptiveSpanEven3495_4 adaptiveSpanWhole3495_4
        adaptiveSpanEvenEntries3495_4 adaptiveSpanWholeEntries3495_4
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanEvenDomain3495_4)
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanWholeDomain3495_4)
  · simpa only [adaptiveSpanLevel3495, adaptiveSpanNumerator3495, adaptiveSpanDenominator3495, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1748) (by decide : 0 < 323)
        adaptiveSpanProfilesValid3495 adaptiveOrder3495 adaptiveSpanNumericCheck3495_5
        adaptiveSpanEven3495_5 adaptiveSpanWhole3495_5
        adaptiveSpanEvenEntries3495_5 adaptiveSpanWholeEntries3495_5
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanEvenDomain3495_5)
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanWholeDomain3495_5)
  · simpa only [adaptiveSpanLevel3495, adaptiveSpanNumerator3495, adaptiveSpanDenominator3495, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1748) (by decide : 0 < 437)
        adaptiveSpanProfilesValid3495 adaptiveOrder3495 adaptiveSpanNumericCheck3495_6
        adaptiveSpanEven3495_6 adaptiveSpanWhole3495_6
        adaptiveSpanEvenEntries3495_6 adaptiveSpanWholeEntries3495_6
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanEvenDomain3495_6)
        (by rw [adaptiveSpanProfileLength3495]; exact adaptiveSpanWholeDomain3495_6)

/-- The complete finite histogram certificate for 3329 ≤ n ≤ 3495. -/
theorem adaptiveSpanHistogram3495 : DegreeIntervalCertificate 3495 adaptiveSpanPrimes3495
    (fun s v => sharpDegree (3329 / 2) 7 (adaptiveSpanNumerator3495 s)
      (adaptiveSpanDenominator3495 s) (totientDensity v))
    (fun s v => sharpDegree 3329 7 (adaptiveSpanNumerator3495 s)
      (adaptiveSpanDenominator3495 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows3495)
    adaptiveSpanPrimes3495
    (fun s => sharpDegree (3329 / 2) 7 (adaptiveSpanNumerator3495 s) (adaptiveSpanDenominator3495 s))
    (fun s => sharpDegree 3329 7 (adaptiveSpanNumerator3495 s) (adaptiveSpanDenominator3495 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid3495 adaptiveOrder3495 (coreOrderPermutationCheck_sound adaptivePermutation3495)
    (by rw [adaptiveSpanProfileLength3495]; decide +kernel)
    adaptiveSpanLevel3495 adaptiveSpanTreeCache3495 adaptiveSpanTreeRepresents3495
    (fun j => adaptiveSpanWitness3495.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck3495

/-- Every required odd cycle for a dense set, throughout 3329 ≤ n ≤ 3495. -/
theorem adaptiveSpanInterval3495 {n : ℕ} (hLn : 3329 ≤ n) (hnU : n ≤ 3495)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes3495
    adaptiveSpanNumerator3495 adaptiveSpanDenominator3495 adaptiveSpanSharpTail3495
    adaptiveSpanPrimeSupport3495 adaptiveSpanHistogram3495 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail3495
#print axioms adaptiveSpanPrimeSupport3495
#print axioms adaptiveSpanHistogram3495
#print axioms adaptiveSpanInterval3495
end Erdos883Verified
