import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate3018Metadata
import Erdos883AdaptiveSpan3018Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes3018 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator3018 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator3018 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail3018 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3018.length) :
    SharpTailCertificate 3018 (adaptiveSpanPrimes3018.take s)
      (adaptiveSpanNumerator3018 s) (adaptiveSpanDenominator3018 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 3018 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3018 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3018 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3018 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3018 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3018 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 3018 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport3018 : ∀ u ∈ oddUniverse 3018,
    ∀ v ∈ oddUniverse 3018, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid3018 : AdaptiveProfileRowsValid adaptiveRows3018 :=
  coreProfileMetadataCheck_sound adaptiveMetadata3018

theorem adaptiveSpanProfileLength3018 : adaptiveRows3018.length = halfOdds 3018 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation3018)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache3018 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3018.length) :
    (adaptiveSpanLevel3018 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel3018 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3018, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3018_0 adaptiveSpanWholeCache3018_0
  · simpa only [adaptiveSpanLevel3018, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3018_1 adaptiveSpanWholeCache3018_1
  · simpa only [adaptiveSpanLevel3018, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3018_2 adaptiveSpanWholeCache3018_2
  · simpa only [adaptiveSpanLevel3018, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3018_3 adaptiveSpanWholeCache3018_3
  · simpa only [adaptiveSpanLevel3018, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3018_4 adaptiveSpanWholeCache3018_4
  · simpa only [adaptiveSpanLevel3018, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3018_5 adaptiveSpanWholeCache3018_5
  · simpa only [adaptiveSpanLevel3018, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache3018_6 adaptiveSpanWholeCache3018_6

theorem adaptiveSpanTreeRepresents3018 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes3018.length) :
    AdaptiveSpanTreeRepresents adaptiveRows3018 (halfOdds 3018)
      (sharpDegree (2875 / 2) 7 (adaptiveSpanNumerator3018 s) (adaptiveSpanDenominator3018 s))
      (sharpDegree 2875 7 (adaptiveSpanNumerator3018 s) (adaptiveSpanDenominator3018 s))
      (adaptiveSpanLevel3018 s).1 (adaptiveSpanLevel3018 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel3018, adaptiveSpanNumerator3018, adaptiveSpanDenominator3018, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1509) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid3018 adaptiveOrder3018 adaptiveSpanNumericCheck3018_0
        adaptiveSpanEven3018_0 adaptiveSpanWhole3018_0
        adaptiveSpanEvenEntries3018_0 adaptiveSpanWholeEntries3018_0
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanEvenDomain3018_0)
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanWholeDomain3018_0)
  · simpa only [adaptiveSpanLevel3018, adaptiveSpanNumerator3018, adaptiveSpanDenominator3018, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1509) (by decide : 0 < 385)
        adaptiveSpanProfilesValid3018 adaptiveOrder3018 adaptiveSpanNumericCheck3018_1
        adaptiveSpanEven3018_1 adaptiveSpanWhole3018_1
        adaptiveSpanEvenEntries3018_1 adaptiveSpanWholeEntries3018_1
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanEvenDomain3018_1)
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanWholeDomain3018_1)
  · simpa only [adaptiveSpanLevel3018, adaptiveSpanNumerator3018, adaptiveSpanDenominator3018, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1509) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid3018 adaptiveOrder3018 adaptiveSpanNumericCheck3018_2
        adaptiveSpanEven3018_2 adaptiveSpanWhole3018_2
        adaptiveSpanEvenEntries3018_2 adaptiveSpanWholeEntries3018_2
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanEvenDomain3018_2)
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanWholeDomain3018_2)
  · simpa only [adaptiveSpanLevel3018, adaptiveSpanNumerator3018, adaptiveSpanDenominator3018, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1509) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid3018 adaptiveOrder3018 adaptiveSpanNumericCheck3018_3
        adaptiveSpanEven3018_3 adaptiveSpanWhole3018_3
        adaptiveSpanEvenEntries3018_3 adaptiveSpanWholeEntries3018_3
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanEvenDomain3018_3)
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanWholeDomain3018_3)
  · simpa only [adaptiveSpanLevel3018, adaptiveSpanNumerator3018, adaptiveSpanDenominator3018, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1509) (by decide : 0 < 221)
        adaptiveSpanProfilesValid3018 adaptiveOrder3018 adaptiveSpanNumericCheck3018_4
        adaptiveSpanEven3018_4 adaptiveSpanWhole3018_4
        adaptiveSpanEvenEntries3018_4 adaptiveSpanWholeEntries3018_4
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanEvenDomain3018_4)
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanWholeDomain3018_4)
  · simpa only [adaptiveSpanLevel3018, adaptiveSpanNumerator3018, adaptiveSpanDenominator3018, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1509) (by decide : 0 < 323)
        adaptiveSpanProfilesValid3018 adaptiveOrder3018 adaptiveSpanNumericCheck3018_5
        adaptiveSpanEven3018_5 adaptiveSpanWhole3018_5
        adaptiveSpanEvenEntries3018_5 adaptiveSpanWholeEntries3018_5
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanEvenDomain3018_5)
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanWholeDomain3018_5)
  · simpa only [adaptiveSpanLevel3018, adaptiveSpanNumerator3018, adaptiveSpanDenominator3018, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 1509) (by decide : 0 < 437)
        adaptiveSpanProfilesValid3018 adaptiveOrder3018 adaptiveSpanNumericCheck3018_6
        adaptiveSpanEven3018_6 adaptiveSpanWhole3018_6
        adaptiveSpanEvenEntries3018_6 adaptiveSpanWholeEntries3018_6
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanEvenDomain3018_6)
        (by rw [adaptiveSpanProfileLength3018]; exact adaptiveSpanWholeDomain3018_6)

/-- The complete finite histogram certificate for 2875 ≤ n ≤ 3018. -/
theorem adaptiveSpanHistogram3018 : DegreeIntervalCertificate 3018 adaptiveSpanPrimes3018
    (fun s v => sharpDegree (2875 / 2) 7 (adaptiveSpanNumerator3018 s)
      (adaptiveSpanDenominator3018 s) (totientDensity v))
    (fun s v => sharpDegree 2875 7 (adaptiveSpanNumerator3018 s)
      (adaptiveSpanDenominator3018 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows3018)
    adaptiveSpanPrimes3018
    (fun s => sharpDegree (2875 / 2) 7 (adaptiveSpanNumerator3018 s) (adaptiveSpanDenominator3018 s))
    (fun s => sharpDegree 2875 7 (adaptiveSpanNumerator3018 s) (adaptiveSpanDenominator3018 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid3018 adaptiveOrder3018 (coreOrderPermutationCheck_sound adaptivePermutation3018)
    (by rw [adaptiveSpanProfileLength3018]; decide +kernel)
    adaptiveSpanLevel3018 adaptiveSpanTreeCache3018 adaptiveSpanTreeRepresents3018
    (fun j => adaptiveSpanWitness3018.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck3018

/-- Every required odd cycle for a dense set, throughout 2875 ≤ n ≤ 3018. -/
theorem adaptiveSpanInterval3018 {n : ℕ} (hLn : 2875 ≤ n) (hnU : n ≤ 3018)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes3018
    adaptiveSpanNumerator3018 adaptiveSpanDenominator3018 adaptiveSpanSharpTail3018
    adaptiveSpanPrimeSupport3018 adaptiveSpanHistogram3018 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail3018
#print axioms adaptiveSpanPrimeSupport3018
#print axioms adaptiveSpanHistogram3018
#print axioms adaptiveSpanInterval3018
end Erdos883Verified
