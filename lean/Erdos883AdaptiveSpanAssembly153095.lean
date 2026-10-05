import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate153095Metadata
import Erdos883AdaptiveSpan153095Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate153095PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes153095 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator153095 : ℕ → ℕ
  | 0 => 5760
  | 1 => 46080
  | 2 => 11520
  | 3 => 34560
  | 4 => 76032
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator153095 : ℕ → ℕ
  | 0 => 15015
  | 1 => 85085
  | 2 => 17017
  | 3 => 46189
  | 4 => 96577
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail153095 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes153095.length) :
    SharpTailCertificate 153095 (adaptiveSpanPrimes153095.take s)
      (adaptiveSpanNumerator153095 s) (adaptiveSpanDenominator153095 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 153095 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 153095 [3] 46080 85085
    refine ⟨by decide, {5, 7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 153095 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 153095 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 153095 [3, 5, 7, 11] 76032 96577
    refine ⟨by decide, {13, 17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 153095 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 153095 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 153095 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 153095 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport153095 : ∀ u ∈ oddUniverse 153095,
    ∀ v ∈ oddUniverse 153095, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid153095 : AdaptiveProfileRowsValid adaptiveRows153095 :=
  coreProfileMetadataCheck_sound adaptiveMetadata153095

theorem adaptiveSpanProfileLength153095 : adaptiveRows153095.length = halfOdds 153095 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics153095
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache153095 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes153095.length) :
    (adaptiveSpanLevel153095 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel153095 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel153095, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache153095_0 adaptiveSpanWholeCache153095_0
  · simpa only [adaptiveSpanLevel153095, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache153095_1 adaptiveSpanWholeCache153095_1
  · simpa only [adaptiveSpanLevel153095, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache153095_2 adaptiveSpanWholeCache153095_2
  · simpa only [adaptiveSpanLevel153095, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache153095_3 adaptiveSpanWholeCache153095_3
  · simpa only [adaptiveSpanLevel153095, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache153095_4 adaptiveSpanWholeCache153095_4
  · simpa only [adaptiveSpanLevel153095, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache153095_5 adaptiveSpanWholeCache153095_5
  · simpa only [adaptiveSpanLevel153095, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache153095_6 adaptiveSpanWholeCache153095_6
  · simpa only [adaptiveSpanLevel153095, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache153095_7 adaptiveSpanWholeCache153095_7
  · simpa only [adaptiveSpanLevel153095, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache153095_8 adaptiveSpanWholeCache153095_8

theorem adaptiveSpanTreeRepresents153095 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes153095.length) :
    AdaptiveSpanTreeRepresents adaptiveRows153095 (halfOdds 153095)
      (sharpDegree (139178 / 2) 9 (adaptiveSpanNumerator153095 s) (adaptiveSpanDenominator153095 s))
      (sharpDegree 139178 9 (adaptiveSpanNumerator153095 s) (adaptiveSpanDenominator153095 s))
      (adaptiveSpanLevel153095 s).1 (adaptiveSpanLevel153095 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel153095, adaptiveSpanNumerator153095, adaptiveSpanDenominator153095, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 76548) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid153095 adaptiveOrder153095 adaptiveSpanNumericCheck153095_0
        adaptiveSpanEven153095_0 adaptiveSpanWhole153095_0
        adaptiveSpanEvenEntries153095_0 adaptiveSpanWholeEntries153095_0
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanEvenDomain153095_0)
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanWholeDomain153095_0)
  · simpa only [adaptiveSpanLevel153095, adaptiveSpanNumerator153095, adaptiveSpanDenominator153095, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 76548) (by decide : 0 < 85085)
        adaptiveSpanProfilesValid153095 adaptiveOrder153095 adaptiveSpanNumericCheck153095_1
        adaptiveSpanEven153095_1 adaptiveSpanWhole153095_1
        adaptiveSpanEvenEntries153095_1 adaptiveSpanWholeEntries153095_1
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanEvenDomain153095_1)
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanWholeDomain153095_1)
  · simpa only [adaptiveSpanLevel153095, adaptiveSpanNumerator153095, adaptiveSpanDenominator153095, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 76548) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid153095 adaptiveOrder153095 adaptiveSpanNumericCheck153095_2
        adaptiveSpanEven153095_2 adaptiveSpanWhole153095_2
        adaptiveSpanEvenEntries153095_2 adaptiveSpanWholeEntries153095_2
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanEvenDomain153095_2)
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanWholeDomain153095_2)
  · simpa only [adaptiveSpanLevel153095, adaptiveSpanNumerator153095, adaptiveSpanDenominator153095, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 76548) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid153095 adaptiveOrder153095 adaptiveSpanNumericCheck153095_3
        adaptiveSpanEven153095_3 adaptiveSpanWhole153095_3
        adaptiveSpanEvenEntries153095_3 adaptiveSpanWholeEntries153095_3
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanEvenDomain153095_3)
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanWholeDomain153095_3)
  · simpa only [adaptiveSpanLevel153095, adaptiveSpanNumerator153095, adaptiveSpanDenominator153095, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 76548) (by decide : 0 < 96577)
        adaptiveSpanProfilesValid153095 adaptiveOrder153095 adaptiveSpanNumericCheck153095_4
        adaptiveSpanEven153095_4 adaptiveSpanWhole153095_4
        adaptiveSpanEvenEntries153095_4 adaptiveSpanWholeEntries153095_4
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanEvenDomain153095_4)
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanWholeDomain153095_4)
  · simpa only [adaptiveSpanLevel153095, adaptiveSpanNumerator153095, adaptiveSpanDenominator153095, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 76548) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid153095 adaptiveOrder153095 adaptiveSpanNumericCheck153095_5
        adaptiveSpanEven153095_5 adaptiveSpanWhole153095_5
        adaptiveSpanEvenEntries153095_5 adaptiveSpanWholeEntries153095_5
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanEvenDomain153095_5)
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanWholeDomain153095_5)
  · simpa only [adaptiveSpanLevel153095, adaptiveSpanNumerator153095, adaptiveSpanDenominator153095, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 76548) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid153095 adaptiveOrder153095 adaptiveSpanNumericCheck153095_6
        adaptiveSpanEven153095_6 adaptiveSpanWhole153095_6
        adaptiveSpanEvenEntries153095_6 adaptiveSpanWholeEntries153095_6
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanEvenDomain153095_6)
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanWholeDomain153095_6)
  · simpa only [adaptiveSpanLevel153095, adaptiveSpanNumerator153095, adaptiveSpanDenominator153095, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 76548) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid153095 adaptiveOrder153095 adaptiveSpanNumericCheck153095_7
        adaptiveSpanEven153095_7 adaptiveSpanWhole153095_7
        adaptiveSpanEvenEntries153095_7 adaptiveSpanWholeEntries153095_7
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanEvenDomain153095_7)
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanWholeDomain153095_7)
  · simpa only [adaptiveSpanLevel153095, adaptiveSpanNumerator153095, adaptiveSpanDenominator153095, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 76548) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid153095 adaptiveOrder153095 adaptiveSpanNumericCheck153095_8
        adaptiveSpanEven153095_8 adaptiveSpanWhole153095_8
        adaptiveSpanEvenEntries153095_8 adaptiveSpanWholeEntries153095_8
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanEvenDomain153095_8)
        (by rw [adaptiveSpanProfileLength153095]; exact adaptiveSpanWholeDomain153095_8)

/-- The complete finite histogram certificate for 139178 ≤ n ≤ 153095. -/
theorem adaptiveSpanHistogram153095 : DegreeIntervalCertificate 153095 adaptiveSpanPrimes153095
    (fun s v => sharpDegree (139178 / 2) 9 (adaptiveSpanNumerator153095 s)
      (adaptiveSpanDenominator153095 s) (totientDensity v))
    (fun s v => sharpDegree 139178 9 (adaptiveSpanNumerator153095 s)
      (adaptiveSpanDenominator153095 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows153095)
    adaptiveSpanPrimes153095
    (fun s => sharpDegree (139178 / 2) 9 (adaptiveSpanNumerator153095 s) (adaptiveSpanDenominator153095 s))
    (fun s => sharpDegree 139178 9 (adaptiveSpanNumerator153095 s) (adaptiveSpanDenominator153095 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid153095 adaptiveOrder153095 adaptivePermutationSemantics153095
    (by rw [adaptiveSpanProfileLength153095]; decide +kernel)
    adaptiveSpanLevel153095 adaptiveSpanTreeCache153095 adaptiveSpanTreeRepresents153095
    (fun j => adaptiveSpanWitness153095.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength153095
  · exact adaptiveSpanWitnessCheck153095

/-- Every required odd cycle for a dense set, throughout 139178 ≤ n ≤ 153095. -/
theorem adaptiveSpanInterval153095 {n : ℕ} (hLn : 139178 ≤ n) (hnU : n ≤ 153095)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes153095
    adaptiveSpanNumerator153095 adaptiveSpanDenominator153095 adaptiveSpanSharpTail153095
    adaptiveSpanPrimeSupport153095 adaptiveSpanHistogram153095 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail153095
#print axioms adaptiveSpanPrimeSupport153095
#print axioms adaptiveSpanHistogram153095
#print axioms adaptiveSpanInterval153095
end Erdos883Verified
