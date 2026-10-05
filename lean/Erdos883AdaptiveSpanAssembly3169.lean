import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate3169Metadata
import Erdos883AdaptiveSpan3169Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes3169 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator3169 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator3169 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail3169 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3169.length) :
    SharpTailCertificate 3169 (adaptiveSpanPrimes3169.take s)
      (adaptiveSpanNumerator3169 s) (adaptiveSpanDenominator3169 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 3169 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3169 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3169 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3169 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3169 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3169 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3169 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport3169 : ∀ u ∈ oddUniverse 3169,
    ∀ v ∈ oddUniverse 3169, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid3169 : AdaptiveProfileRowsValid adaptiveRows3169 :=
  coreProfileMetadataCheck_sound adaptiveMetadata3169

theorem adaptiveSpanProfileLength3169 : adaptiveRows3169.length = halfOdds 3169 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation3169)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache3169 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3169.length) :
    (adaptiveSpanLevel3169 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel3169 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3169, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3169_0 adaptiveSpanWholeCache3169_0
  · simpa only [adaptiveSpanLevel3169, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3169_1 adaptiveSpanWholeCache3169_1
  · simpa only [adaptiveSpanLevel3169, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3169_2 adaptiveSpanWholeCache3169_2
  · simpa only [adaptiveSpanLevel3169, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3169_3 adaptiveSpanWholeCache3169_3
  · simpa only [adaptiveSpanLevel3169, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3169_4 adaptiveSpanWholeCache3169_4
  · simpa only [adaptiveSpanLevel3169, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3169_5 adaptiveSpanWholeCache3169_5
  · simpa only [adaptiveSpanLevel3169, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3169_6 adaptiveSpanWholeCache3169_6

theorem adaptiveSpanTreeRepresents3169 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3169.length) :
    AdaptiveSpanTreeRepresents adaptiveRows3169 (halfOdds 3169)
      (sharpDegree (3019 / 2) 7 (adaptiveSpanNumerator3169 s) (adaptiveSpanDenominator3169 s))
      (sharpDegree 3019 7 (adaptiveSpanNumerator3169 s) (adaptiveSpanDenominator3169 s))
      (adaptiveSpanLevel3169 s).1 (adaptiveSpanLevel3169 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3169, adaptiveSpanNumerator3169, adaptiveSpanDenominator3169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1585) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid3169 adaptiveOrder3169 adaptiveSpanNumericCheck3169_0
        adaptiveSpanEven3169_0 adaptiveSpanWhole3169_0
        adaptiveSpanEvenEntries3169_0 adaptiveSpanWholeEntries3169_0
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanEvenDomain3169_0)
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanWholeDomain3169_0)
  · simpa only [adaptiveSpanLevel3169, adaptiveSpanNumerator3169, adaptiveSpanDenominator3169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1585) (by decide : 0 < 385)
        adaptiveSpanProfilesValid3169 adaptiveOrder3169 adaptiveSpanNumericCheck3169_1
        adaptiveSpanEven3169_1 adaptiveSpanWhole3169_1
        adaptiveSpanEvenEntries3169_1 adaptiveSpanWholeEntries3169_1
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanEvenDomain3169_1)
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanWholeDomain3169_1)
  · simpa only [adaptiveSpanLevel3169, adaptiveSpanNumerator3169, adaptiveSpanDenominator3169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1585) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid3169 adaptiveOrder3169 adaptiveSpanNumericCheck3169_2
        adaptiveSpanEven3169_2 adaptiveSpanWhole3169_2
        adaptiveSpanEvenEntries3169_2 adaptiveSpanWholeEntries3169_2
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanEvenDomain3169_2)
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanWholeDomain3169_2)
  · simpa only [adaptiveSpanLevel3169, adaptiveSpanNumerator3169, adaptiveSpanDenominator3169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1585) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid3169 adaptiveOrder3169 adaptiveSpanNumericCheck3169_3
        adaptiveSpanEven3169_3 adaptiveSpanWhole3169_3
        adaptiveSpanEvenEntries3169_3 adaptiveSpanWholeEntries3169_3
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanEvenDomain3169_3)
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanWholeDomain3169_3)
  · simpa only [adaptiveSpanLevel3169, adaptiveSpanNumerator3169, adaptiveSpanDenominator3169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1585) (by decide : 0 < 221)
        adaptiveSpanProfilesValid3169 adaptiveOrder3169 adaptiveSpanNumericCheck3169_4
        adaptiveSpanEven3169_4 adaptiveSpanWhole3169_4
        adaptiveSpanEvenEntries3169_4 adaptiveSpanWholeEntries3169_4
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanEvenDomain3169_4)
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanWholeDomain3169_4)
  · simpa only [adaptiveSpanLevel3169, adaptiveSpanNumerator3169, adaptiveSpanDenominator3169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1585) (by decide : 0 < 323)
        adaptiveSpanProfilesValid3169 adaptiveOrder3169 adaptiveSpanNumericCheck3169_5
        adaptiveSpanEven3169_5 adaptiveSpanWhole3169_5
        adaptiveSpanEvenEntries3169_5 adaptiveSpanWholeEntries3169_5
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanEvenDomain3169_5)
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanWholeDomain3169_5)
  · simpa only [adaptiveSpanLevel3169, adaptiveSpanNumerator3169, adaptiveSpanDenominator3169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1585) (by decide : 0 < 437)
        adaptiveSpanProfilesValid3169 adaptiveOrder3169 adaptiveSpanNumericCheck3169_6
        adaptiveSpanEven3169_6 adaptiveSpanWhole3169_6
        adaptiveSpanEvenEntries3169_6 adaptiveSpanWholeEntries3169_6
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanEvenDomain3169_6)
        (by rw [adaptiveSpanProfileLength3169]; exact adaptiveSpanWholeDomain3169_6)

/-- The complete finite histogram certificate for 3019 ≤ n ≤ 3169. -/
theorem adaptiveSpanHistogram3169 : DegreeIntervalCertificate 3169 adaptiveSpanPrimes3169
    (fun s v => sharpDegree (3019 / 2) 7 (adaptiveSpanNumerator3169 s)
      (adaptiveSpanDenominator3169 s) (totientDensity v))
    (fun s v => sharpDegree 3019 7 (adaptiveSpanNumerator3169 s)
      (adaptiveSpanDenominator3169 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows3169)
    adaptiveSpanPrimes3169
    (fun s => sharpDegree (3019 / 2) 7 (adaptiveSpanNumerator3169 s) (adaptiveSpanDenominator3169 s))
    (fun s => sharpDegree 3019 7 (adaptiveSpanNumerator3169 s) (adaptiveSpanDenominator3169 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid3169 adaptiveOrder3169 (coreOrderPermutationCheck_sound adaptivePermutation3169)
    (by rw [adaptiveSpanProfileLength3169]; decide +kernel)
    adaptiveSpanLevel3169 adaptiveSpanTreeCache3169 adaptiveSpanTreeRepresents3169
    (fun j => adaptiveSpanWitness3169.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck3169

/-- Every required odd cycle for a dense set, throughout 3019 ≤ n ≤ 3169. -/
theorem adaptiveSpanInterval3169 {n : ℕ} (hLn : 3019 ≤ n) (hnU : n ≤ 3169)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes3169
    adaptiveSpanNumerator3169 adaptiveSpanDenominator3169 adaptiveSpanSharpTail3169
    adaptiveSpanPrimeSupport3169 adaptiveSpanHistogram3169 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail3169
#print axioms adaptiveSpanPrimeSupport3169
#print axioms adaptiveSpanHistogram3169
#print axioms adaptiveSpanInterval3169
end Erdos883Verified
