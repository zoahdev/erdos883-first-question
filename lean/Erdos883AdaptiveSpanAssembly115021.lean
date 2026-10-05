import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate115021Metadata
import Erdos883AdaptiveSpan115021Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate115021PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes115021 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator115021 : ℕ → ℕ
  | 0 => 5760
  | 1 => 46080
  | 2 => 11520
  | 3 => 34560
  | 4 => 76032
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator115021 : ℕ → ℕ
  | 0 => 15015
  | 1 => 85085
  | 2 => 17017
  | 3 => 46189
  | 4 => 96577
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail115021 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes115021.length) :
    SharpTailCertificate 115021 (adaptiveSpanPrimes115021.take s)
      (adaptiveSpanNumerator115021 s) (adaptiveSpanDenominator115021 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 115021 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 115021 [3] 46080 85085
    refine ⟨by decide, {5, 7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 115021 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 115021 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 115021 [3, 5, 7, 11] 76032 96577
    refine ⟨by decide, {13, 17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 115021 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 115021 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 115021 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 115021 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport115021 : ∀ u ∈ oddUniverse 115021,
    ∀ v ∈ oddUniverse 115021, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid115021 : AdaptiveProfileRowsValid adaptiveRows115021 :=
  coreProfileMetadataCheck_sound adaptiveMetadata115021

theorem adaptiveSpanProfileLength115021 : adaptiveRows115021.length = halfOdds 115021 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics115021
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache115021 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes115021.length) :
    (adaptiveSpanLevel115021 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel115021 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel115021, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache115021_0 adaptiveSpanWholeCache115021_0
  · simpa only [adaptiveSpanLevel115021, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache115021_1 adaptiveSpanWholeCache115021_1
  · simpa only [adaptiveSpanLevel115021, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache115021_2 adaptiveSpanWholeCache115021_2
  · simpa only [adaptiveSpanLevel115021, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache115021_3 adaptiveSpanWholeCache115021_3
  · simpa only [adaptiveSpanLevel115021, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache115021_4 adaptiveSpanWholeCache115021_4
  · simpa only [adaptiveSpanLevel115021, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache115021_5 adaptiveSpanWholeCache115021_5
  · simpa only [adaptiveSpanLevel115021, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache115021_6 adaptiveSpanWholeCache115021_6
  · simpa only [adaptiveSpanLevel115021, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache115021_7 adaptiveSpanWholeCache115021_7
  · simpa only [adaptiveSpanLevel115021, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache115021_8 adaptiveSpanWholeCache115021_8

theorem adaptiveSpanTreeRepresents115021 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes115021.length) :
    AdaptiveSpanTreeRepresents adaptiveRows115021 (halfOdds 115021)
      (sharpDegree (104565 / 2) 9 (adaptiveSpanNumerator115021 s) (adaptiveSpanDenominator115021 s))
      (sharpDegree 104565 9 (adaptiveSpanNumerator115021 s) (adaptiveSpanDenominator115021 s))
      (adaptiveSpanLevel115021 s).1 (adaptiveSpanLevel115021 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel115021, adaptiveSpanNumerator115021, adaptiveSpanDenominator115021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 57511) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid115021 adaptiveOrder115021 adaptiveSpanNumericCheck115021_0
        adaptiveSpanEven115021_0 adaptiveSpanWhole115021_0
        adaptiveSpanEvenEntries115021_0 adaptiveSpanWholeEntries115021_0
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanEvenDomain115021_0)
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanWholeDomain115021_0)
  · simpa only [adaptiveSpanLevel115021, adaptiveSpanNumerator115021, adaptiveSpanDenominator115021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 57511) (by decide : 0 < 85085)
        adaptiveSpanProfilesValid115021 adaptiveOrder115021 adaptiveSpanNumericCheck115021_1
        adaptiveSpanEven115021_1 adaptiveSpanWhole115021_1
        adaptiveSpanEvenEntries115021_1 adaptiveSpanWholeEntries115021_1
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanEvenDomain115021_1)
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanWholeDomain115021_1)
  · simpa only [adaptiveSpanLevel115021, adaptiveSpanNumerator115021, adaptiveSpanDenominator115021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 57511) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid115021 adaptiveOrder115021 adaptiveSpanNumericCheck115021_2
        adaptiveSpanEven115021_2 adaptiveSpanWhole115021_2
        adaptiveSpanEvenEntries115021_2 adaptiveSpanWholeEntries115021_2
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanEvenDomain115021_2)
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanWholeDomain115021_2)
  · simpa only [adaptiveSpanLevel115021, adaptiveSpanNumerator115021, adaptiveSpanDenominator115021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 57511) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid115021 adaptiveOrder115021 adaptiveSpanNumericCheck115021_3
        adaptiveSpanEven115021_3 adaptiveSpanWhole115021_3
        adaptiveSpanEvenEntries115021_3 adaptiveSpanWholeEntries115021_3
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanEvenDomain115021_3)
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanWholeDomain115021_3)
  · simpa only [adaptiveSpanLevel115021, adaptiveSpanNumerator115021, adaptiveSpanDenominator115021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 57511) (by decide : 0 < 96577)
        adaptiveSpanProfilesValid115021 adaptiveOrder115021 adaptiveSpanNumericCheck115021_4
        adaptiveSpanEven115021_4 adaptiveSpanWhole115021_4
        adaptiveSpanEvenEntries115021_4 adaptiveSpanWholeEntries115021_4
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanEvenDomain115021_4)
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanWholeDomain115021_4)
  · simpa only [adaptiveSpanLevel115021, adaptiveSpanNumerator115021, adaptiveSpanDenominator115021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 57511) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid115021 adaptiveOrder115021 adaptiveSpanNumericCheck115021_5
        adaptiveSpanEven115021_5 adaptiveSpanWhole115021_5
        adaptiveSpanEvenEntries115021_5 adaptiveSpanWholeEntries115021_5
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanEvenDomain115021_5)
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanWholeDomain115021_5)
  · simpa only [adaptiveSpanLevel115021, adaptiveSpanNumerator115021, adaptiveSpanDenominator115021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 57511) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid115021 adaptiveOrder115021 adaptiveSpanNumericCheck115021_6
        adaptiveSpanEven115021_6 adaptiveSpanWhole115021_6
        adaptiveSpanEvenEntries115021_6 adaptiveSpanWholeEntries115021_6
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanEvenDomain115021_6)
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanWholeDomain115021_6)
  · simpa only [adaptiveSpanLevel115021, adaptiveSpanNumerator115021, adaptiveSpanDenominator115021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 57511) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid115021 adaptiveOrder115021 adaptiveSpanNumericCheck115021_7
        adaptiveSpanEven115021_7 adaptiveSpanWhole115021_7
        adaptiveSpanEvenEntries115021_7 adaptiveSpanWholeEntries115021_7
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanEvenDomain115021_7)
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanWholeDomain115021_7)
  · simpa only [adaptiveSpanLevel115021, adaptiveSpanNumerator115021, adaptiveSpanDenominator115021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 57511) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid115021 adaptiveOrder115021 adaptiveSpanNumericCheck115021_8
        adaptiveSpanEven115021_8 adaptiveSpanWhole115021_8
        adaptiveSpanEvenEntries115021_8 adaptiveSpanWholeEntries115021_8
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanEvenDomain115021_8)
        (by rw [adaptiveSpanProfileLength115021]; exact adaptiveSpanWholeDomain115021_8)

/-- The complete finite histogram certificate for 104565 ≤ n ≤ 115021. -/
theorem adaptiveSpanHistogram115021 : DegreeIntervalCertificate 115021 adaptiveSpanPrimes115021
    (fun s v => sharpDegree (104565 / 2) 9 (adaptiveSpanNumerator115021 s)
      (adaptiveSpanDenominator115021 s) (totientDensity v))
    (fun s v => sharpDegree 104565 9 (adaptiveSpanNumerator115021 s)
      (adaptiveSpanDenominator115021 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows115021)
    adaptiveSpanPrimes115021
    (fun s => sharpDegree (104565 / 2) 9 (adaptiveSpanNumerator115021 s) (adaptiveSpanDenominator115021 s))
    (fun s => sharpDegree 104565 9 (adaptiveSpanNumerator115021 s) (adaptiveSpanDenominator115021 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid115021 adaptiveOrder115021 adaptivePermutationSemantics115021
    (by rw [adaptiveSpanProfileLength115021]; decide +kernel)
    adaptiveSpanLevel115021 adaptiveSpanTreeCache115021 adaptiveSpanTreeRepresents115021
    (fun j => adaptiveSpanWitness115021.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength115021
  · exact adaptiveSpanWitnessCheck115021

/-- Every required odd cycle for a dense set, throughout 104565 ≤ n ≤ 115021. -/
theorem adaptiveSpanInterval115021 {n : ℕ} (hLn : 104565 ≤ n) (hnU : n ≤ 115021)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes115021
    adaptiveSpanNumerator115021 adaptiveSpanDenominator115021 adaptiveSpanSharpTail115021
    adaptiveSpanPrimeSupport115021 adaptiveSpanHistogram115021 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail115021
#print axioms adaptiveSpanPrimeSupport115021
#print axioms adaptiveSpanHistogram115021
#print axioms adaptiveSpanInterval115021
end Erdos883Verified
