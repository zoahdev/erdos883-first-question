import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate3670Metadata
import Erdos883AdaptiveSpan3670Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes3670 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator3670 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator3670 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail3670 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3670.length) :
    SharpTailCertificate 3670 (adaptiveSpanPrimes3670.take s)
      (adaptiveSpanNumerator3670 s) (adaptiveSpanDenominator3670 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 3670 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3670 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3670 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3670 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3670 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3670 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3670 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport3670 : ∀ u ∈ oddUniverse 3670,
    ∀ v ∈ oddUniverse 3670, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid3670 : AdaptiveProfileRowsValid adaptiveRows3670 :=
  coreProfileMetadataCheck_sound adaptiveMetadata3670

theorem adaptiveSpanProfileLength3670 : adaptiveRows3670.length = halfOdds 3670 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation3670)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache3670 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3670.length) :
    (adaptiveSpanLevel3670 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel3670 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3670, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3670_0 adaptiveSpanWholeCache3670_0
  · simpa only [adaptiveSpanLevel3670, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3670_1 adaptiveSpanWholeCache3670_1
  · simpa only [adaptiveSpanLevel3670, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3670_2 adaptiveSpanWholeCache3670_2
  · simpa only [adaptiveSpanLevel3670, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3670_3 adaptiveSpanWholeCache3670_3
  · simpa only [adaptiveSpanLevel3670, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3670_4 adaptiveSpanWholeCache3670_4
  · simpa only [adaptiveSpanLevel3670, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3670_5 adaptiveSpanWholeCache3670_5
  · simpa only [adaptiveSpanLevel3670, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3670_6 adaptiveSpanWholeCache3670_6

theorem adaptiveSpanTreeRepresents3670 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3670.length) :
    AdaptiveSpanTreeRepresents adaptiveRows3670 (halfOdds 3670)
      (sharpDegree (3496 / 2) 7 (adaptiveSpanNumerator3670 s) (adaptiveSpanDenominator3670 s))
      (sharpDegree 3496 7 (adaptiveSpanNumerator3670 s) (adaptiveSpanDenominator3670 s))
      (adaptiveSpanLevel3670 s).1 (adaptiveSpanLevel3670 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3670, adaptiveSpanNumerator3670, adaptiveSpanDenominator3670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1835) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid3670 adaptiveOrder3670 adaptiveSpanNumericCheck3670_0
        adaptiveSpanEven3670_0 adaptiveSpanWhole3670_0
        adaptiveSpanEvenEntries3670_0 adaptiveSpanWholeEntries3670_0
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanEvenDomain3670_0)
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanWholeDomain3670_0)
  · simpa only [adaptiveSpanLevel3670, adaptiveSpanNumerator3670, adaptiveSpanDenominator3670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1835) (by decide : 0 < 385)
        adaptiveSpanProfilesValid3670 adaptiveOrder3670 adaptiveSpanNumericCheck3670_1
        adaptiveSpanEven3670_1 adaptiveSpanWhole3670_1
        adaptiveSpanEvenEntries3670_1 adaptiveSpanWholeEntries3670_1
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanEvenDomain3670_1)
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanWholeDomain3670_1)
  · simpa only [adaptiveSpanLevel3670, adaptiveSpanNumerator3670, adaptiveSpanDenominator3670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1835) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid3670 adaptiveOrder3670 adaptiveSpanNumericCheck3670_2
        adaptiveSpanEven3670_2 adaptiveSpanWhole3670_2
        adaptiveSpanEvenEntries3670_2 adaptiveSpanWholeEntries3670_2
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanEvenDomain3670_2)
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanWholeDomain3670_2)
  · simpa only [adaptiveSpanLevel3670, adaptiveSpanNumerator3670, adaptiveSpanDenominator3670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1835) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid3670 adaptiveOrder3670 adaptiveSpanNumericCheck3670_3
        adaptiveSpanEven3670_3 adaptiveSpanWhole3670_3
        adaptiveSpanEvenEntries3670_3 adaptiveSpanWholeEntries3670_3
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanEvenDomain3670_3)
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanWholeDomain3670_3)
  · simpa only [adaptiveSpanLevel3670, adaptiveSpanNumerator3670, adaptiveSpanDenominator3670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1835) (by decide : 0 < 221)
        adaptiveSpanProfilesValid3670 adaptiveOrder3670 adaptiveSpanNumericCheck3670_4
        adaptiveSpanEven3670_4 adaptiveSpanWhole3670_4
        adaptiveSpanEvenEntries3670_4 adaptiveSpanWholeEntries3670_4
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanEvenDomain3670_4)
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanWholeDomain3670_4)
  · simpa only [adaptiveSpanLevel3670, adaptiveSpanNumerator3670, adaptiveSpanDenominator3670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1835) (by decide : 0 < 323)
        adaptiveSpanProfilesValid3670 adaptiveOrder3670 adaptiveSpanNumericCheck3670_5
        adaptiveSpanEven3670_5 adaptiveSpanWhole3670_5
        adaptiveSpanEvenEntries3670_5 adaptiveSpanWholeEntries3670_5
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanEvenDomain3670_5)
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanWholeDomain3670_5)
  · simpa only [adaptiveSpanLevel3670, adaptiveSpanNumerator3670, adaptiveSpanDenominator3670, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1835) (by decide : 0 < 437)
        adaptiveSpanProfilesValid3670 adaptiveOrder3670 adaptiveSpanNumericCheck3670_6
        adaptiveSpanEven3670_6 adaptiveSpanWhole3670_6
        adaptiveSpanEvenEntries3670_6 adaptiveSpanWholeEntries3670_6
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanEvenDomain3670_6)
        (by rw [adaptiveSpanProfileLength3670]; exact adaptiveSpanWholeDomain3670_6)

/-- The complete finite histogram certificate for 3496 ≤ n ≤ 3670. -/
theorem adaptiveSpanHistogram3670 : DegreeIntervalCertificate 3670 adaptiveSpanPrimes3670
    (fun s v => sharpDegree (3496 / 2) 7 (adaptiveSpanNumerator3670 s)
      (adaptiveSpanDenominator3670 s) (totientDensity v))
    (fun s v => sharpDegree 3496 7 (adaptiveSpanNumerator3670 s)
      (adaptiveSpanDenominator3670 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows3670)
    adaptiveSpanPrimes3670
    (fun s => sharpDegree (3496 / 2) 7 (adaptiveSpanNumerator3670 s) (adaptiveSpanDenominator3670 s))
    (fun s => sharpDegree 3496 7 (adaptiveSpanNumerator3670 s) (adaptiveSpanDenominator3670 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid3670 adaptiveOrder3670 (coreOrderPermutationCheck_sound adaptivePermutation3670)
    (by rw [adaptiveSpanProfileLength3670]; decide +kernel)
    adaptiveSpanLevel3670 adaptiveSpanTreeCache3670 adaptiveSpanTreeRepresents3670
    (fun j => adaptiveSpanWitness3670.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck3670

/-- Every required odd cycle for a dense set, throughout 3496 ≤ n ≤ 3670. -/
theorem adaptiveSpanInterval3670 {n : ℕ} (hLn : 3496 ≤ n) (hnU : n ≤ 3670)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes3670
    adaptiveSpanNumerator3670 adaptiveSpanDenominator3670 adaptiveSpanSharpTail3670
    adaptiveSpanPrimeSupport3670 adaptiveSpanHistogram3670 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail3670
#print axioms adaptiveSpanPrimeSupport3670
#print axioms adaptiveSpanHistogram3670
#print axioms adaptiveSpanInterval3670
end Erdos883Verified
