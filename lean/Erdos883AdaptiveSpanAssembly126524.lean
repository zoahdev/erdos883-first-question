import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate126524Metadata
import Erdos883AdaptiveSpan126524Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate126524PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes126524 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator126524 : ℕ → ℕ
  | 0 => 5760
  | 1 => 46080
  | 2 => 11520
  | 3 => 34560
  | 4 => 76032
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator126524 : ℕ → ℕ
  | 0 => 15015
  | 1 => 85085
  | 2 => 17017
  | 3 => 46189
  | 4 => 96577
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail126524 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes126524.length) :
    SharpTailCertificate 126524 (adaptiveSpanPrimes126524.take s)
      (adaptiveSpanNumerator126524 s) (adaptiveSpanDenominator126524 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 126524 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 126524 [3] 46080 85085
    refine ⟨by decide, {5, 7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 126524 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 126524 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 126524 [3, 5, 7, 11] 76032 96577
    refine ⟨by decide, {13, 17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 126524 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 126524 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 126524 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 126524 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport126524 : ∀ u ∈ oddUniverse 126524,
    ∀ v ∈ oddUniverse 126524, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid126524 : AdaptiveProfileRowsValid adaptiveRows126524 :=
  coreProfileMetadataCheck_sound adaptiveMetadata126524

theorem adaptiveSpanProfileLength126524 : adaptiveRows126524.length = halfOdds 126524 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics126524
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache126524 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes126524.length) :
    (adaptiveSpanLevel126524 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel126524 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel126524, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache126524_0 adaptiveSpanWholeCache126524_0
  · simpa only [adaptiveSpanLevel126524, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache126524_1 adaptiveSpanWholeCache126524_1
  · simpa only [adaptiveSpanLevel126524, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache126524_2 adaptiveSpanWholeCache126524_2
  · simpa only [adaptiveSpanLevel126524, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache126524_3 adaptiveSpanWholeCache126524_3
  · simpa only [adaptiveSpanLevel126524, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache126524_4 adaptiveSpanWholeCache126524_4
  · simpa only [adaptiveSpanLevel126524, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache126524_5 adaptiveSpanWholeCache126524_5
  · simpa only [adaptiveSpanLevel126524, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache126524_6 adaptiveSpanWholeCache126524_6
  · simpa only [adaptiveSpanLevel126524, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache126524_7 adaptiveSpanWholeCache126524_7
  · simpa only [adaptiveSpanLevel126524, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache126524_8 adaptiveSpanWholeCache126524_8

theorem adaptiveSpanTreeRepresents126524 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes126524.length) :
    AdaptiveSpanTreeRepresents adaptiveRows126524 (halfOdds 126524)
      (sharpDegree (115022 / 2) 9 (adaptiveSpanNumerator126524 s) (adaptiveSpanDenominator126524 s))
      (sharpDegree 115022 9 (adaptiveSpanNumerator126524 s) (adaptiveSpanDenominator126524 s))
      (adaptiveSpanLevel126524 s).1 (adaptiveSpanLevel126524 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel126524, adaptiveSpanNumerator126524, adaptiveSpanDenominator126524, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 63262) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid126524 adaptiveOrder126524 adaptiveSpanNumericCheck126524_0
        adaptiveSpanEven126524_0 adaptiveSpanWhole126524_0
        adaptiveSpanEvenEntries126524_0 adaptiveSpanWholeEntries126524_0
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanEvenDomain126524_0)
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanWholeDomain126524_0)
  · simpa only [adaptiveSpanLevel126524, adaptiveSpanNumerator126524, adaptiveSpanDenominator126524, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 63262) (by decide : 0 < 85085)
        adaptiveSpanProfilesValid126524 adaptiveOrder126524 adaptiveSpanNumericCheck126524_1
        adaptiveSpanEven126524_1 adaptiveSpanWhole126524_1
        adaptiveSpanEvenEntries126524_1 adaptiveSpanWholeEntries126524_1
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanEvenDomain126524_1)
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanWholeDomain126524_1)
  · simpa only [adaptiveSpanLevel126524, adaptiveSpanNumerator126524, adaptiveSpanDenominator126524, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 63262) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid126524 adaptiveOrder126524 adaptiveSpanNumericCheck126524_2
        adaptiveSpanEven126524_2 adaptiveSpanWhole126524_2
        adaptiveSpanEvenEntries126524_2 adaptiveSpanWholeEntries126524_2
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanEvenDomain126524_2)
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanWholeDomain126524_2)
  · simpa only [adaptiveSpanLevel126524, adaptiveSpanNumerator126524, adaptiveSpanDenominator126524, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 63262) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid126524 adaptiveOrder126524 adaptiveSpanNumericCheck126524_3
        adaptiveSpanEven126524_3 adaptiveSpanWhole126524_3
        adaptiveSpanEvenEntries126524_3 adaptiveSpanWholeEntries126524_3
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanEvenDomain126524_3)
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanWholeDomain126524_3)
  · simpa only [adaptiveSpanLevel126524, adaptiveSpanNumerator126524, adaptiveSpanDenominator126524, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 63262) (by decide : 0 < 96577)
        adaptiveSpanProfilesValid126524 adaptiveOrder126524 adaptiveSpanNumericCheck126524_4
        adaptiveSpanEven126524_4 adaptiveSpanWhole126524_4
        adaptiveSpanEvenEntries126524_4 adaptiveSpanWholeEntries126524_4
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanEvenDomain126524_4)
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanWholeDomain126524_4)
  · simpa only [adaptiveSpanLevel126524, adaptiveSpanNumerator126524, adaptiveSpanDenominator126524, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 63262) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid126524 adaptiveOrder126524 adaptiveSpanNumericCheck126524_5
        adaptiveSpanEven126524_5 adaptiveSpanWhole126524_5
        adaptiveSpanEvenEntries126524_5 adaptiveSpanWholeEntries126524_5
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanEvenDomain126524_5)
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanWholeDomain126524_5)
  · simpa only [adaptiveSpanLevel126524, adaptiveSpanNumerator126524, adaptiveSpanDenominator126524, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 63262) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid126524 adaptiveOrder126524 adaptiveSpanNumericCheck126524_6
        adaptiveSpanEven126524_6 adaptiveSpanWhole126524_6
        adaptiveSpanEvenEntries126524_6 adaptiveSpanWholeEntries126524_6
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanEvenDomain126524_6)
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanWholeDomain126524_6)
  · simpa only [adaptiveSpanLevel126524, adaptiveSpanNumerator126524, adaptiveSpanDenominator126524, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 63262) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid126524 adaptiveOrder126524 adaptiveSpanNumericCheck126524_7
        adaptiveSpanEven126524_7 adaptiveSpanWhole126524_7
        adaptiveSpanEvenEntries126524_7 adaptiveSpanWholeEntries126524_7
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanEvenDomain126524_7)
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanWholeDomain126524_7)
  · simpa only [adaptiveSpanLevel126524, adaptiveSpanNumerator126524, adaptiveSpanDenominator126524, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 63262) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid126524 adaptiveOrder126524 adaptiveSpanNumericCheck126524_8
        adaptiveSpanEven126524_8 adaptiveSpanWhole126524_8
        adaptiveSpanEvenEntries126524_8 adaptiveSpanWholeEntries126524_8
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanEvenDomain126524_8)
        (by rw [adaptiveSpanProfileLength126524]; exact adaptiveSpanWholeDomain126524_8)

/-- The complete finite histogram certificate for 115022 ≤ n ≤ 126524. -/
theorem adaptiveSpanHistogram126524 : DegreeIntervalCertificate 126524 adaptiveSpanPrimes126524
    (fun s v => sharpDegree (115022 / 2) 9 (adaptiveSpanNumerator126524 s)
      (adaptiveSpanDenominator126524 s) (totientDensity v))
    (fun s v => sharpDegree 115022 9 (adaptiveSpanNumerator126524 s)
      (adaptiveSpanDenominator126524 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows126524)
    adaptiveSpanPrimes126524
    (fun s => sharpDegree (115022 / 2) 9 (adaptiveSpanNumerator126524 s) (adaptiveSpanDenominator126524 s))
    (fun s => sharpDegree 115022 9 (adaptiveSpanNumerator126524 s) (adaptiveSpanDenominator126524 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid126524 adaptiveOrder126524 adaptivePermutationSemantics126524
    (by rw [adaptiveSpanProfileLength126524]; decide +kernel)
    adaptiveSpanLevel126524 adaptiveSpanTreeCache126524 adaptiveSpanTreeRepresents126524
    (fun j => adaptiveSpanWitness126524.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength126524
  · exact adaptiveSpanWitnessCheck126524

/-- Every required odd cycle for a dense set, throughout 115022 ≤ n ≤ 126524. -/
theorem adaptiveSpanInterval126524 {n : ℕ} (hLn : 115022 ≤ n) (hnU : n ≤ 126524)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes126524
    adaptiveSpanNumerator126524 adaptiveSpanDenominator126524 adaptiveSpanSharpTail126524
    adaptiveSpanPrimeSupport126524 adaptiveSpanHistogram126524 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail126524
#print axioms adaptiveSpanPrimeSupport126524
#print axioms adaptiveSpanHistogram126524
#print axioms adaptiveSpanInterval126524
end Erdos883Verified
