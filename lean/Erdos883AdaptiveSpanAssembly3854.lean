import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate3854Metadata
import Erdos883AdaptiveSpan3854Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes3854 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator3854 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator3854 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail3854 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3854.length) :
    SharpTailCertificate 3854 (adaptiveSpanPrimes3854.take s)
      (adaptiveSpanNumerator3854 s) (adaptiveSpanDenominator3854 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 3854 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3854 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3854 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3854 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3854 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3854 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3854 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport3854 : ∀ u ∈ oddUniverse 3854,
    ∀ v ∈ oddUniverse 3854, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid3854 : AdaptiveProfileRowsValid adaptiveRows3854 :=
  coreProfileMetadataCheck_sound adaptiveMetadata3854

theorem adaptiveSpanProfileLength3854 : adaptiveRows3854.length = halfOdds 3854 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation3854)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache3854 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3854.length) :
    (adaptiveSpanLevel3854 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel3854 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3854, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3854_0 adaptiveSpanWholeCache3854_0
  · simpa only [adaptiveSpanLevel3854, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3854_1 adaptiveSpanWholeCache3854_1
  · simpa only [adaptiveSpanLevel3854, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3854_2 adaptiveSpanWholeCache3854_2
  · simpa only [adaptiveSpanLevel3854, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3854_3 adaptiveSpanWholeCache3854_3
  · simpa only [adaptiveSpanLevel3854, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3854_4 adaptiveSpanWholeCache3854_4
  · simpa only [adaptiveSpanLevel3854, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3854_5 adaptiveSpanWholeCache3854_5
  · simpa only [adaptiveSpanLevel3854, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3854_6 adaptiveSpanWholeCache3854_6

theorem adaptiveSpanTreeRepresents3854 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3854.length) :
    AdaptiveSpanTreeRepresents adaptiveRows3854 (halfOdds 3854)
      (sharpDegree (3671 / 2) 7 (adaptiveSpanNumerator3854 s) (adaptiveSpanDenominator3854 s))
      (sharpDegree 3671 7 (adaptiveSpanNumerator3854 s) (adaptiveSpanDenominator3854 s))
      (adaptiveSpanLevel3854 s).1 (adaptiveSpanLevel3854 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3854, adaptiveSpanNumerator3854, adaptiveSpanDenominator3854, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1927) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid3854 adaptiveOrder3854 adaptiveSpanNumericCheck3854_0
        adaptiveSpanEven3854_0 adaptiveSpanWhole3854_0
        adaptiveSpanEvenEntries3854_0 adaptiveSpanWholeEntries3854_0
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanEvenDomain3854_0)
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanWholeDomain3854_0)
  · simpa only [adaptiveSpanLevel3854, adaptiveSpanNumerator3854, adaptiveSpanDenominator3854, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1927) (by decide : 0 < 385)
        adaptiveSpanProfilesValid3854 adaptiveOrder3854 adaptiveSpanNumericCheck3854_1
        adaptiveSpanEven3854_1 adaptiveSpanWhole3854_1
        adaptiveSpanEvenEntries3854_1 adaptiveSpanWholeEntries3854_1
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanEvenDomain3854_1)
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanWholeDomain3854_1)
  · simpa only [adaptiveSpanLevel3854, adaptiveSpanNumerator3854, adaptiveSpanDenominator3854, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1927) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid3854 adaptiveOrder3854 adaptiveSpanNumericCheck3854_2
        adaptiveSpanEven3854_2 adaptiveSpanWhole3854_2
        adaptiveSpanEvenEntries3854_2 adaptiveSpanWholeEntries3854_2
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanEvenDomain3854_2)
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanWholeDomain3854_2)
  · simpa only [adaptiveSpanLevel3854, adaptiveSpanNumerator3854, adaptiveSpanDenominator3854, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1927) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid3854 adaptiveOrder3854 adaptiveSpanNumericCheck3854_3
        adaptiveSpanEven3854_3 adaptiveSpanWhole3854_3
        adaptiveSpanEvenEntries3854_3 adaptiveSpanWholeEntries3854_3
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanEvenDomain3854_3)
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanWholeDomain3854_3)
  · simpa only [adaptiveSpanLevel3854, adaptiveSpanNumerator3854, adaptiveSpanDenominator3854, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1927) (by decide : 0 < 221)
        adaptiveSpanProfilesValid3854 adaptiveOrder3854 adaptiveSpanNumericCheck3854_4
        adaptiveSpanEven3854_4 adaptiveSpanWhole3854_4
        adaptiveSpanEvenEntries3854_4 adaptiveSpanWholeEntries3854_4
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanEvenDomain3854_4)
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanWholeDomain3854_4)
  · simpa only [adaptiveSpanLevel3854, adaptiveSpanNumerator3854, adaptiveSpanDenominator3854, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1927) (by decide : 0 < 323)
        adaptiveSpanProfilesValid3854 adaptiveOrder3854 adaptiveSpanNumericCheck3854_5
        adaptiveSpanEven3854_5 adaptiveSpanWhole3854_5
        adaptiveSpanEvenEntries3854_5 adaptiveSpanWholeEntries3854_5
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanEvenDomain3854_5)
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanWholeDomain3854_5)
  · simpa only [adaptiveSpanLevel3854, adaptiveSpanNumerator3854, adaptiveSpanDenominator3854, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1927) (by decide : 0 < 437)
        adaptiveSpanProfilesValid3854 adaptiveOrder3854 adaptiveSpanNumericCheck3854_6
        adaptiveSpanEven3854_6 adaptiveSpanWhole3854_6
        adaptiveSpanEvenEntries3854_6 adaptiveSpanWholeEntries3854_6
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanEvenDomain3854_6)
        (by rw [adaptiveSpanProfileLength3854]; exact adaptiveSpanWholeDomain3854_6)

/-- The complete finite histogram certificate for 3671 ≤ n ≤ 3854. -/
theorem adaptiveSpanHistogram3854 : DegreeIntervalCertificate 3854 adaptiveSpanPrimes3854
    (fun s v => sharpDegree (3671 / 2) 7 (adaptiveSpanNumerator3854 s)
      (adaptiveSpanDenominator3854 s) (totientDensity v))
    (fun s v => sharpDegree 3671 7 (adaptiveSpanNumerator3854 s)
      (adaptiveSpanDenominator3854 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows3854)
    adaptiveSpanPrimes3854
    (fun s => sharpDegree (3671 / 2) 7 (adaptiveSpanNumerator3854 s) (adaptiveSpanDenominator3854 s))
    (fun s => sharpDegree 3671 7 (adaptiveSpanNumerator3854 s) (adaptiveSpanDenominator3854 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid3854 adaptiveOrder3854 (coreOrderPermutationCheck_sound adaptivePermutation3854)
    (by rw [adaptiveSpanProfileLength3854]; decide +kernel)
    adaptiveSpanLevel3854 adaptiveSpanTreeCache3854 adaptiveSpanTreeRepresents3854
    (fun j => adaptiveSpanWitness3854.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck3854

/-- Every required odd cycle for a dense set, throughout 3671 ≤ n ≤ 3854. -/
theorem adaptiveSpanInterval3854 {n : ℕ} (hLn : 3671 ≤ n) (hnU : n ≤ 3854)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes3854
    adaptiveSpanNumerator3854 adaptiveSpanDenominator3854 adaptiveSpanSharpTail3854
    adaptiveSpanPrimeSupport3854 adaptiveSpanHistogram3854 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail3854
#print axioms adaptiveSpanPrimeSupport3854
#print axioms adaptiveSpanHistogram3854
#print axioms adaptiveSpanInterval3854
end Erdos883Verified
