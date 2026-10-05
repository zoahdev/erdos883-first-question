import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate8767Metadata
import Erdos883AdaptiveSpan8767Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes8767 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator8767 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 396
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator8767 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 437
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail8767 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes8767.length) :
    SharpTailCertificate 8767 (adaptiveSpanPrimes8767.take s)
      (adaptiveSpanNumerator8767 s) (adaptiveSpanDenominator8767 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 8767 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 8767 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 8767 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 8767 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 8767 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 8767 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 8767 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 8767 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 8767 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport8767 : ∀ u ∈ oddUniverse 8767,
    ∀ v ∈ oddUniverse 8767, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid8767 : AdaptiveProfileRowsValid adaptiveRows8767 :=
  coreProfileMetadataCheck_sound adaptiveMetadata8767

theorem adaptiveSpanProfileLength8767 : adaptiveRows8767.length = halfOdds 8767 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation8767)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache8767 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes8767.length) :
    (adaptiveSpanLevel8767 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel8767 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel8767, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache8767_0 adaptiveSpanWholeCache8767_0
  · simpa only [adaptiveSpanLevel8767, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache8767_1 adaptiveSpanWholeCache8767_1
  · simpa only [adaptiveSpanLevel8767, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache8767_2 adaptiveSpanWholeCache8767_2
  · simpa only [adaptiveSpanLevel8767, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache8767_3 adaptiveSpanWholeCache8767_3
  · simpa only [adaptiveSpanLevel8767, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache8767_4 adaptiveSpanWholeCache8767_4
  · simpa only [adaptiveSpanLevel8767, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache8767_5 adaptiveSpanWholeCache8767_5
  · simpa only [adaptiveSpanLevel8767, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache8767_6 adaptiveSpanWholeCache8767_6
  · simpa only [adaptiveSpanLevel8767, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache8767_7 adaptiveSpanWholeCache8767_7
  · simpa only [adaptiveSpanLevel8767, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache8767_8 adaptiveSpanWholeCache8767_8

theorem adaptiveSpanTreeRepresents8767 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes8767.length) :
    AdaptiveSpanTreeRepresents adaptiveRows8767 (halfOdds 8767)
      (sharpDegree (7970 / 2) 7 (adaptiveSpanNumerator8767 s) (adaptiveSpanDenominator8767 s))
      (sharpDegree 7970 7 (adaptiveSpanNumerator8767 s) (adaptiveSpanDenominator8767 s))
      (adaptiveSpanLevel8767 s).1 (adaptiveSpanLevel8767 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel8767, adaptiveSpanNumerator8767, adaptiveSpanDenominator8767, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4384) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid8767 adaptiveOrder8767 adaptiveSpanNumericCheck8767_0
        adaptiveSpanEven8767_0 adaptiveSpanWhole8767_0
        adaptiveSpanEvenEntries8767_0 adaptiveSpanWholeEntries8767_0
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanEvenDomain8767_0)
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanWholeDomain8767_0)
  · simpa only [adaptiveSpanLevel8767, adaptiveSpanNumerator8767, adaptiveSpanDenominator8767, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4384) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid8767 adaptiveOrder8767 adaptiveSpanNumericCheck8767_1
        adaptiveSpanEven8767_1 adaptiveSpanWhole8767_1
        adaptiveSpanEvenEntries8767_1 adaptiveSpanWholeEntries8767_1
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanEvenDomain8767_1)
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanWholeDomain8767_1)
  · simpa only [adaptiveSpanLevel8767, adaptiveSpanNumerator8767, adaptiveSpanDenominator8767, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4384) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid8767 adaptiveOrder8767 adaptiveSpanNumericCheck8767_2
        adaptiveSpanEven8767_2 adaptiveSpanWhole8767_2
        adaptiveSpanEvenEntries8767_2 adaptiveSpanWholeEntries8767_2
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanEvenDomain8767_2)
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanWholeDomain8767_2)
  · simpa only [adaptiveSpanLevel8767, adaptiveSpanNumerator8767, adaptiveSpanDenominator8767, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4384) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid8767 adaptiveOrder8767 adaptiveSpanNumericCheck8767_3
        adaptiveSpanEven8767_3 adaptiveSpanWhole8767_3
        adaptiveSpanEvenEntries8767_3 adaptiveSpanWholeEntries8767_3
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanEvenDomain8767_3)
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanWholeDomain8767_3)
  · simpa only [adaptiveSpanLevel8767, adaptiveSpanNumerator8767, adaptiveSpanDenominator8767, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4384) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid8767 adaptiveOrder8767 adaptiveSpanNumericCheck8767_4
        adaptiveSpanEven8767_4 adaptiveSpanWhole8767_4
        adaptiveSpanEvenEntries8767_4 adaptiveSpanWholeEntries8767_4
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanEvenDomain8767_4)
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanWholeDomain8767_4)
  · simpa only [adaptiveSpanLevel8767, adaptiveSpanNumerator8767, adaptiveSpanDenominator8767, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4384) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid8767 adaptiveOrder8767 adaptiveSpanNumericCheck8767_5
        adaptiveSpanEven8767_5 adaptiveSpanWhole8767_5
        adaptiveSpanEvenEntries8767_5 adaptiveSpanWholeEntries8767_5
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanEvenDomain8767_5)
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanWholeDomain8767_5)
  · simpa only [adaptiveSpanLevel8767, adaptiveSpanNumerator8767, adaptiveSpanDenominator8767, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4384) (by decide : 0 < 437)
        adaptiveSpanProfilesValid8767 adaptiveOrder8767 adaptiveSpanNumericCheck8767_6
        adaptiveSpanEven8767_6 adaptiveSpanWhole8767_6
        adaptiveSpanEvenEntries8767_6 adaptiveSpanWholeEntries8767_6
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanEvenDomain8767_6)
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanWholeDomain8767_6)
  · simpa only [adaptiveSpanLevel8767, adaptiveSpanNumerator8767, adaptiveSpanDenominator8767, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4384) (by decide : 0 < 667)
        adaptiveSpanProfilesValid8767 adaptiveOrder8767 adaptiveSpanNumericCheck8767_7
        adaptiveSpanEven8767_7 adaptiveSpanWhole8767_7
        adaptiveSpanEvenEntries8767_7 adaptiveSpanWholeEntries8767_7
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanEvenDomain8767_7)
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanWholeDomain8767_7)
  · simpa only [adaptiveSpanLevel8767, adaptiveSpanNumerator8767, adaptiveSpanDenominator8767, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4384) (by decide : 0 < 899)
        adaptiveSpanProfilesValid8767 adaptiveOrder8767 adaptiveSpanNumericCheck8767_8
        adaptiveSpanEven8767_8 adaptiveSpanWhole8767_8
        adaptiveSpanEvenEntries8767_8 adaptiveSpanWholeEntries8767_8
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanEvenDomain8767_8)
        (by rw [adaptiveSpanProfileLength8767]; exact adaptiveSpanWholeDomain8767_8)

/-- The complete finite histogram certificate for 7970 ≤ n ≤ 8767. -/
theorem adaptiveSpanHistogram8767 : DegreeIntervalCertificate 8767 adaptiveSpanPrimes8767
    (fun s v => sharpDegree (7970 / 2) 7 (adaptiveSpanNumerator8767 s)
      (adaptiveSpanDenominator8767 s) (totientDensity v))
    (fun s v => sharpDegree 7970 7 (adaptiveSpanNumerator8767 s)
      (adaptiveSpanDenominator8767 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows8767)
    adaptiveSpanPrimes8767
    (fun s => sharpDegree (7970 / 2) 7 (adaptiveSpanNumerator8767 s) (adaptiveSpanDenominator8767 s))
    (fun s => sharpDegree 7970 7 (adaptiveSpanNumerator8767 s) (adaptiveSpanDenominator8767 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid8767 adaptiveOrder8767 (coreOrderPermutationCheck_sound adaptivePermutation8767)
    (by rw [adaptiveSpanProfileLength8767]; decide +kernel)
    adaptiveSpanLevel8767 adaptiveSpanTreeCache8767 adaptiveSpanTreeRepresents8767
    (fun j => adaptiveSpanWitness8767.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck8767

/-- Every required odd cycle for a dense set, throughout 7970 ≤ n ≤ 8767. -/
theorem adaptiveSpanInterval8767 {n : ℕ} (hLn : 7970 ≤ n) (hnU : n ≤ 8767)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes8767
    adaptiveSpanNumerator8767 adaptiveSpanDenominator8767 adaptiveSpanSharpTail8767
    adaptiveSpanPrimeSupport8767 adaptiveSpanHistogram8767 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail8767
#print axioms adaptiveSpanPrimeSupport8767
#print axioms adaptiveSpanHistogram8767
#print axioms adaptiveSpanInterval8767
end Erdos883Verified
