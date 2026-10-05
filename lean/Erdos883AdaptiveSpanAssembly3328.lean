import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate3328Metadata
import Erdos883AdaptiveSpan3328Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes3328 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator3328 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator3328 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail3328 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3328.length) :
    SharpTailCertificate 3328 (adaptiveSpanPrimes3328.take s)
      (adaptiveSpanNumerator3328 s) (adaptiveSpanDenominator3328 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 3328 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3328 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3328 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3328 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3328 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3328 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3328 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport3328 : ∀ u ∈ oddUniverse 3328,
    ∀ v ∈ oddUniverse 3328, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid3328 : AdaptiveProfileRowsValid adaptiveRows3328 :=
  coreProfileMetadataCheck_sound adaptiveMetadata3328

theorem adaptiveSpanProfileLength3328 : adaptiveRows3328.length = halfOdds 3328 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation3328)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache3328 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3328.length) :
    (adaptiveSpanLevel3328 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel3328 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3328, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3328_0 adaptiveSpanWholeCache3328_0
  · simpa only [adaptiveSpanLevel3328, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3328_1 adaptiveSpanWholeCache3328_1
  · simpa only [adaptiveSpanLevel3328, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3328_2 adaptiveSpanWholeCache3328_2
  · simpa only [adaptiveSpanLevel3328, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3328_3 adaptiveSpanWholeCache3328_3
  · simpa only [adaptiveSpanLevel3328, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3328_4 adaptiveSpanWholeCache3328_4
  · simpa only [adaptiveSpanLevel3328, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3328_5 adaptiveSpanWholeCache3328_5
  · simpa only [adaptiveSpanLevel3328, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3328_6 adaptiveSpanWholeCache3328_6

theorem adaptiveSpanTreeRepresents3328 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3328.length) :
    AdaptiveSpanTreeRepresents adaptiveRows3328 (halfOdds 3328)
      (sharpDegree (3170 / 2) 7 (adaptiveSpanNumerator3328 s) (adaptiveSpanDenominator3328 s))
      (sharpDegree 3170 7 (adaptiveSpanNumerator3328 s) (adaptiveSpanDenominator3328 s))
      (adaptiveSpanLevel3328 s).1 (adaptiveSpanLevel3328 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3328, adaptiveSpanNumerator3328, adaptiveSpanDenominator3328, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1664) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid3328 adaptiveOrder3328 adaptiveSpanNumericCheck3328_0
        adaptiveSpanEven3328_0 adaptiveSpanWhole3328_0
        adaptiveSpanEvenEntries3328_0 adaptiveSpanWholeEntries3328_0
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanEvenDomain3328_0)
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanWholeDomain3328_0)
  · simpa only [adaptiveSpanLevel3328, adaptiveSpanNumerator3328, adaptiveSpanDenominator3328, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1664) (by decide : 0 < 385)
        adaptiveSpanProfilesValid3328 adaptiveOrder3328 adaptiveSpanNumericCheck3328_1
        adaptiveSpanEven3328_1 adaptiveSpanWhole3328_1
        adaptiveSpanEvenEntries3328_1 adaptiveSpanWholeEntries3328_1
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanEvenDomain3328_1)
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanWholeDomain3328_1)
  · simpa only [adaptiveSpanLevel3328, adaptiveSpanNumerator3328, adaptiveSpanDenominator3328, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1664) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid3328 adaptiveOrder3328 adaptiveSpanNumericCheck3328_2
        adaptiveSpanEven3328_2 adaptiveSpanWhole3328_2
        adaptiveSpanEvenEntries3328_2 adaptiveSpanWholeEntries3328_2
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanEvenDomain3328_2)
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanWholeDomain3328_2)
  · simpa only [adaptiveSpanLevel3328, adaptiveSpanNumerator3328, adaptiveSpanDenominator3328, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1664) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid3328 adaptiveOrder3328 adaptiveSpanNumericCheck3328_3
        adaptiveSpanEven3328_3 adaptiveSpanWhole3328_3
        adaptiveSpanEvenEntries3328_3 adaptiveSpanWholeEntries3328_3
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanEvenDomain3328_3)
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanWholeDomain3328_3)
  · simpa only [adaptiveSpanLevel3328, adaptiveSpanNumerator3328, adaptiveSpanDenominator3328, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1664) (by decide : 0 < 221)
        adaptiveSpanProfilesValid3328 adaptiveOrder3328 adaptiveSpanNumericCheck3328_4
        adaptiveSpanEven3328_4 adaptiveSpanWhole3328_4
        adaptiveSpanEvenEntries3328_4 adaptiveSpanWholeEntries3328_4
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanEvenDomain3328_4)
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanWholeDomain3328_4)
  · simpa only [adaptiveSpanLevel3328, adaptiveSpanNumerator3328, adaptiveSpanDenominator3328, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1664) (by decide : 0 < 323)
        adaptiveSpanProfilesValid3328 adaptiveOrder3328 adaptiveSpanNumericCheck3328_5
        adaptiveSpanEven3328_5 adaptiveSpanWhole3328_5
        adaptiveSpanEvenEntries3328_5 adaptiveSpanWholeEntries3328_5
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanEvenDomain3328_5)
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanWholeDomain3328_5)
  · simpa only [adaptiveSpanLevel3328, adaptiveSpanNumerator3328, adaptiveSpanDenominator3328, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1664) (by decide : 0 < 437)
        adaptiveSpanProfilesValid3328 adaptiveOrder3328 adaptiveSpanNumericCheck3328_6
        adaptiveSpanEven3328_6 adaptiveSpanWhole3328_6
        adaptiveSpanEvenEntries3328_6 adaptiveSpanWholeEntries3328_6
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanEvenDomain3328_6)
        (by rw [adaptiveSpanProfileLength3328]; exact adaptiveSpanWholeDomain3328_6)

/-- The complete finite histogram certificate for 3170 ≤ n ≤ 3328. -/
theorem adaptiveSpanHistogram3328 : DegreeIntervalCertificate 3328 adaptiveSpanPrimes3328
    (fun s v => sharpDegree (3170 / 2) 7 (adaptiveSpanNumerator3328 s)
      (adaptiveSpanDenominator3328 s) (totientDensity v))
    (fun s v => sharpDegree 3170 7 (adaptiveSpanNumerator3328 s)
      (adaptiveSpanDenominator3328 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows3328)
    adaptiveSpanPrimes3328
    (fun s => sharpDegree (3170 / 2) 7 (adaptiveSpanNumerator3328 s) (adaptiveSpanDenominator3328 s))
    (fun s => sharpDegree 3170 7 (adaptiveSpanNumerator3328 s) (adaptiveSpanDenominator3328 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid3328 adaptiveOrder3328 (coreOrderPermutationCheck_sound adaptivePermutation3328)
    (by rw [adaptiveSpanProfileLength3328]; decide +kernel)
    adaptiveSpanLevel3328 adaptiveSpanTreeCache3328 adaptiveSpanTreeRepresents3328
    (fun j => adaptiveSpanWitness3328.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck3328

/-- Every required odd cycle for a dense set, throughout 3170 ≤ n ≤ 3328. -/
theorem adaptiveSpanInterval3328 {n : ℕ} (hLn : 3170 ≤ n) (hnU : n ≤ 3328)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes3328
    adaptiveSpanNumerator3328 adaptiveSpanDenominator3328 adaptiveSpanSharpTail3328
    adaptiveSpanPrimeSupport3328 adaptiveSpanHistogram3328 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail3328
#print axioms adaptiveSpanPrimeSupport3328
#print axioms adaptiveSpanHistogram3328
#print axioms adaptiveSpanInterval3328
end Erdos883Verified
