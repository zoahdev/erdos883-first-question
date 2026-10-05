import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate59021Metadata
import Erdos883AdaptiveSpan59021Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate59021PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes59021 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29]

def adaptiveSpanNumerator59021 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 34560
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | 8 => 30240
  | _ => 43200

def adaptiveSpanDenominator59021 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 46189
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | 8 => 33263
  | _ => 47027

theorem adaptiveSpanSharpTail59021 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes59021.length) :
    SharpTailCertificate 59021 (adaptiveSpanPrimes59021.take s)
      (adaptiveSpanNumerator59021 s) (adaptiveSpanDenominator59021 s) := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 59021 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 59021 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 59021 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 59021 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 59021 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 59021 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 59021 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 59021 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 59021 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 59021 [3, 5, 7, 11, 13, 17, 19, 23, 29] 43200 47027
    refine ⟨by decide, {31, 37, 41}, 43, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport59021 : ∀ u ∈ oddUniverse 59021,
    ∀ v ∈ oddUniverse 59021, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid59021 : AdaptiveProfileRowsValid adaptiveRows59021 :=
  coreProfileMetadataCheck_sound adaptiveMetadata59021

theorem adaptiveSpanProfileLength59021 : adaptiveRows59021.length = halfOdds 59021 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics59021
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache59021 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes59021.length) :
    (adaptiveSpanLevel59021 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel59021 s).2.cacheCheck = true := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel59021, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache59021_0 adaptiveSpanWholeCache59021_0
  · simpa only [adaptiveSpanLevel59021, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache59021_1 adaptiveSpanWholeCache59021_1
  · simpa only [adaptiveSpanLevel59021, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache59021_2 adaptiveSpanWholeCache59021_2
  · simpa only [adaptiveSpanLevel59021, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache59021_3 adaptiveSpanWholeCache59021_3
  · simpa only [adaptiveSpanLevel59021, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache59021_4 adaptiveSpanWholeCache59021_4
  · simpa only [adaptiveSpanLevel59021, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache59021_5 adaptiveSpanWholeCache59021_5
  · simpa only [adaptiveSpanLevel59021, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache59021_6 adaptiveSpanWholeCache59021_6
  · simpa only [adaptiveSpanLevel59021, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache59021_7 adaptiveSpanWholeCache59021_7
  · simpa only [adaptiveSpanLevel59021, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache59021_8 adaptiveSpanWholeCache59021_8
  · simpa only [adaptiveSpanLevel59021, (show (9 : ℕ) ≠ 0 by decide), (show (9 : ℕ) ≠ 1 by decide), (show (9 : ℕ) ≠ 2 by decide), (show (9 : ℕ) ≠ 3 by decide), (show (9 : ℕ) ≠ 4 by decide), (show (9 : ℕ) ≠ 5 by decide), (show (9 : ℕ) ≠ 6 by decide), (show (9 : ℕ) ≠ 7 by decide), (show (9 : ℕ) ≠ 8 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache59021_9 adaptiveSpanWholeCache59021_9

theorem adaptiveSpanTreeRepresents59021 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes59021.length) :
    AdaptiveSpanTreeRepresents adaptiveRows59021 (halfOdds 59021)
      (sharpDegree (53656 / 2) 9 (adaptiveSpanNumerator59021 s) (adaptiveSpanDenominator59021 s))
      (sharpDegree 53656 9 (adaptiveSpanNumerator59021 s) (adaptiveSpanDenominator59021 s))
      (adaptiveSpanLevel59021 s).1 (adaptiveSpanLevel59021 s).2 := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel59021, adaptiveSpanNumerator59021, adaptiveSpanDenominator59021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 29511) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptiveSpanNumericCheck59021_0
        adaptiveSpanEven59021_0 adaptiveSpanWhole59021_0
        adaptiveSpanEvenEntries59021_0 adaptiveSpanWholeEntries59021_0
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanEvenDomain59021_0)
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanWholeDomain59021_0)
  · simpa only [adaptiveSpanLevel59021, adaptiveSpanNumerator59021, adaptiveSpanDenominator59021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 29511) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptiveSpanNumericCheck59021_1
        adaptiveSpanEven59021_1 adaptiveSpanWhole59021_1
        adaptiveSpanEvenEntries59021_1 adaptiveSpanWholeEntries59021_1
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanEvenDomain59021_1)
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanWholeDomain59021_1)
  · simpa only [adaptiveSpanLevel59021, adaptiveSpanNumerator59021, adaptiveSpanDenominator59021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 29511) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptiveSpanNumericCheck59021_2
        adaptiveSpanEven59021_2 adaptiveSpanWhole59021_2
        adaptiveSpanEvenEntries59021_2 adaptiveSpanWholeEntries59021_2
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanEvenDomain59021_2)
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanWholeDomain59021_2)
  · simpa only [adaptiveSpanLevel59021, adaptiveSpanNumerator59021, adaptiveSpanDenominator59021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 29511) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptiveSpanNumericCheck59021_3
        adaptiveSpanEven59021_3 adaptiveSpanWhole59021_3
        adaptiveSpanEvenEntries59021_3 adaptiveSpanWholeEntries59021_3
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanEvenDomain59021_3)
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanWholeDomain59021_3)
  · simpa only [adaptiveSpanLevel59021, adaptiveSpanNumerator59021, adaptiveSpanDenominator59021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 29511) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptiveSpanNumericCheck59021_4
        adaptiveSpanEven59021_4 adaptiveSpanWhole59021_4
        adaptiveSpanEvenEntries59021_4 adaptiveSpanWholeEntries59021_4
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanEvenDomain59021_4)
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanWholeDomain59021_4)
  · simpa only [adaptiveSpanLevel59021, adaptiveSpanNumerator59021, adaptiveSpanDenominator59021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 29511) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptiveSpanNumericCheck59021_5
        adaptiveSpanEven59021_5 adaptiveSpanWhole59021_5
        adaptiveSpanEvenEntries59021_5 adaptiveSpanWholeEntries59021_5
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanEvenDomain59021_5)
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanWholeDomain59021_5)
  · simpa only [adaptiveSpanLevel59021, adaptiveSpanNumerator59021, adaptiveSpanDenominator59021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 29511) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptiveSpanNumericCheck59021_6
        adaptiveSpanEven59021_6 adaptiveSpanWhole59021_6
        adaptiveSpanEvenEntries59021_6 adaptiveSpanWholeEntries59021_6
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanEvenDomain59021_6)
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanWholeDomain59021_6)
  · simpa only [adaptiveSpanLevel59021, adaptiveSpanNumerator59021, adaptiveSpanDenominator59021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 29511) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptiveSpanNumericCheck59021_7
        adaptiveSpanEven59021_7 adaptiveSpanWhole59021_7
        adaptiveSpanEvenEntries59021_7 adaptiveSpanWholeEntries59021_7
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanEvenDomain59021_7)
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanWholeDomain59021_7)
  · simpa only [adaptiveSpanLevel59021, adaptiveSpanNumerator59021, adaptiveSpanDenominator59021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 29511) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptiveSpanNumericCheck59021_8
        adaptiveSpanEven59021_8 adaptiveSpanWhole59021_8
        adaptiveSpanEvenEntries59021_8 adaptiveSpanWholeEntries59021_8
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanEvenDomain59021_8)
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanWholeDomain59021_8)
  · simpa only [adaptiveSpanLevel59021, adaptiveSpanNumerator59021, adaptiveSpanDenominator59021, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (9 : ℕ) ≠ 0 by decide), (show (9 : ℕ) ≠ 1 by decide), (show (9 : ℕ) ≠ 2 by decide), (show (9 : ℕ) ≠ 3 by decide), (show (9 : ℕ) ≠ 4 by decide), (show (9 : ℕ) ≠ 5 by decide), (show (9 : ℕ) ≠ 6 by decide), (show (9 : ℕ) ≠ 7 by decide), (show (9 : ℕ) ≠ 8 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 29511) (by decide : 0 < 47027)
        adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptiveSpanNumericCheck59021_9
        adaptiveSpanEven59021_9 adaptiveSpanWhole59021_9
        adaptiveSpanEvenEntries59021_9 adaptiveSpanWholeEntries59021_9
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanEvenDomain59021_9)
        (by rw [adaptiveSpanProfileLength59021]; exact adaptiveSpanWholeDomain59021_9)

/-- The complete finite histogram certificate for 53656 ≤ n ≤ 59021. -/
theorem adaptiveSpanHistogram59021 : DegreeIntervalCertificate 59021 adaptiveSpanPrimes59021
    (fun s v => sharpDegree (53656 / 2) 9 (adaptiveSpanNumerator59021 s)
      (adaptiveSpanDenominator59021 s) (totientDensity v))
    (fun s v => sharpDegree 53656 9 (adaptiveSpanNumerator59021 s)
      (adaptiveSpanDenominator59021 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows59021)
    adaptiveSpanPrimes59021
    (fun s => sharpDegree (53656 / 2) 9 (adaptiveSpanNumerator59021 s) (adaptiveSpanDenominator59021 s))
    (fun s => sharpDegree 53656 9 (adaptiveSpanNumerator59021 s) (adaptiveSpanDenominator59021 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid59021 adaptiveOrder59021 adaptivePermutationSemantics59021
    (by rw [adaptiveSpanProfileLength59021]; decide +kernel)
    adaptiveSpanLevel59021 adaptiveSpanTreeCache59021 adaptiveSpanTreeRepresents59021
    (fun j => adaptiveSpanWitness59021.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength59021
  · exact adaptiveSpanWitnessCheck59021

/-- Every required odd cycle for a dense set, throughout 53656 ≤ n ≤ 59021. -/
theorem adaptiveSpanInterval59021 {n : ℕ} (hLn : 53656 ≤ n) (hnU : n ≤ 59021)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes59021
    adaptiveSpanNumerator59021 adaptiveSpanDenominator59021 adaptiveSpanSharpTail59021
    adaptiveSpanPrimeSupport59021 adaptiveSpanHistogram59021 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail59021
#print axioms adaptiveSpanPrimeSupport59021
#print axioms adaptiveSpanHistogram59021
#print axioms adaptiveSpanInterval59021
end Erdos883Verified
