import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate36645Metadata
import Erdos883AdaptiveSpan36645Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate36645PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes36645 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29]

def adaptiveSpanNumerator36645 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | 8 => 30240
  | _ => 1080

def adaptiveSpanDenominator36645 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | 8 => 33263
  | _ => 1147

theorem adaptiveSpanSharpTail36645 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes36645.length) :
    SharpTailCertificate 36645 (adaptiveSpanPrimes36645.take s)
      (adaptiveSpanNumerator36645 s) (adaptiveSpanDenominator36645 s) := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 36645 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 36645 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 36645 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 36645 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 36645 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 36645 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 36645 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 36645 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 36645 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 36645 [3, 5, 7, 11, 13, 17, 19, 23, 29] 1080 1147
    refine ⟨by decide, {31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport36645 : ∀ u ∈ oddUniverse 36645,
    ∀ v ∈ oddUniverse 36645, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid36645 : AdaptiveProfileRowsValid adaptiveRows36645 :=
  coreProfileMetadataCheck_sound adaptiveMetadata36645

theorem adaptiveSpanProfileLength36645 : adaptiveRows36645.length = halfOdds 36645 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics36645
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache36645 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes36645.length) :
    (adaptiveSpanLevel36645 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel36645 s).2.cacheCheck = true := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel36645, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache36645_0 adaptiveSpanWholeCache36645_0
  · simpa only [adaptiveSpanLevel36645, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache36645_1 adaptiveSpanWholeCache36645_1
  · simpa only [adaptiveSpanLevel36645, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache36645_2 adaptiveSpanWholeCache36645_2
  · simpa only [adaptiveSpanLevel36645, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache36645_3 adaptiveSpanWholeCache36645_3
  · simpa only [adaptiveSpanLevel36645, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache36645_4 adaptiveSpanWholeCache36645_4
  · simpa only [adaptiveSpanLevel36645, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache36645_5 adaptiveSpanWholeCache36645_5
  · simpa only [adaptiveSpanLevel36645, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache36645_6 adaptiveSpanWholeCache36645_6
  · simpa only [adaptiveSpanLevel36645, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache36645_7 adaptiveSpanWholeCache36645_7
  · simpa only [adaptiveSpanLevel36645, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache36645_8 adaptiveSpanWholeCache36645_8
  · simpa only [adaptiveSpanLevel36645, (show (9 : ℕ) ≠ 0 by decide), (show (9 : ℕ) ≠ 1 by decide), (show (9 : ℕ) ≠ 2 by decide), (show (9 : ℕ) ≠ 3 by decide), (show (9 : ℕ) ≠ 4 by decide), (show (9 : ℕ) ≠ 5 by decide), (show (9 : ℕ) ≠ 6 by decide), (show (9 : ℕ) ≠ 7 by decide), (show (9 : ℕ) ≠ 8 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache36645_9 adaptiveSpanWholeCache36645_9

theorem adaptiveSpanTreeRepresents36645 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes36645.length) :
    AdaptiveSpanTreeRepresents adaptiveRows36645 (halfOdds 36645)
      (sharpDegree (33314 / 2) 8 (adaptiveSpanNumerator36645 s) (adaptiveSpanDenominator36645 s))
      (sharpDegree 33314 8 (adaptiveSpanNumerator36645 s) (adaptiveSpanDenominator36645 s))
      (adaptiveSpanLevel36645 s).1 (adaptiveSpanLevel36645 s).2 := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel36645, adaptiveSpanNumerator36645, adaptiveSpanDenominator36645, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 18323) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptiveSpanNumericCheck36645_0
        adaptiveSpanEven36645_0 adaptiveSpanWhole36645_0
        adaptiveSpanEvenEntries36645_0 adaptiveSpanWholeEntries36645_0
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanEvenDomain36645_0)
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanWholeDomain36645_0)
  · simpa only [adaptiveSpanLevel36645, adaptiveSpanNumerator36645, adaptiveSpanDenominator36645, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 18323) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptiveSpanNumericCheck36645_1
        adaptiveSpanEven36645_1 adaptiveSpanWhole36645_1
        adaptiveSpanEvenEntries36645_1 adaptiveSpanWholeEntries36645_1
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanEvenDomain36645_1)
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanWholeDomain36645_1)
  · simpa only [adaptiveSpanLevel36645, adaptiveSpanNumerator36645, adaptiveSpanDenominator36645, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 18323) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptiveSpanNumericCheck36645_2
        adaptiveSpanEven36645_2 adaptiveSpanWhole36645_2
        adaptiveSpanEvenEntries36645_2 adaptiveSpanWholeEntries36645_2
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanEvenDomain36645_2)
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanWholeDomain36645_2)
  · simpa only [adaptiveSpanLevel36645, adaptiveSpanNumerator36645, adaptiveSpanDenominator36645, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 18323) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptiveSpanNumericCheck36645_3
        adaptiveSpanEven36645_3 adaptiveSpanWhole36645_3
        adaptiveSpanEvenEntries36645_3 adaptiveSpanWholeEntries36645_3
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanEvenDomain36645_3)
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanWholeDomain36645_3)
  · simpa only [adaptiveSpanLevel36645, adaptiveSpanNumerator36645, adaptiveSpanDenominator36645, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 18323) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptiveSpanNumericCheck36645_4
        adaptiveSpanEven36645_4 adaptiveSpanWhole36645_4
        adaptiveSpanEvenEntries36645_4 adaptiveSpanWholeEntries36645_4
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanEvenDomain36645_4)
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanWholeDomain36645_4)
  · simpa only [adaptiveSpanLevel36645, adaptiveSpanNumerator36645, adaptiveSpanDenominator36645, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 18323) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptiveSpanNumericCheck36645_5
        adaptiveSpanEven36645_5 adaptiveSpanWhole36645_5
        adaptiveSpanEvenEntries36645_5 adaptiveSpanWholeEntries36645_5
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanEvenDomain36645_5)
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanWholeDomain36645_5)
  · simpa only [adaptiveSpanLevel36645, adaptiveSpanNumerator36645, adaptiveSpanDenominator36645, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 18323) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptiveSpanNumericCheck36645_6
        adaptiveSpanEven36645_6 adaptiveSpanWhole36645_6
        adaptiveSpanEvenEntries36645_6 adaptiveSpanWholeEntries36645_6
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanEvenDomain36645_6)
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanWholeDomain36645_6)
  · simpa only [adaptiveSpanLevel36645, adaptiveSpanNumerator36645, adaptiveSpanDenominator36645, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 18323) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptiveSpanNumericCheck36645_7
        adaptiveSpanEven36645_7 adaptiveSpanWhole36645_7
        adaptiveSpanEvenEntries36645_7 adaptiveSpanWholeEntries36645_7
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanEvenDomain36645_7)
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanWholeDomain36645_7)
  · simpa only [adaptiveSpanLevel36645, adaptiveSpanNumerator36645, adaptiveSpanDenominator36645, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 18323) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptiveSpanNumericCheck36645_8
        adaptiveSpanEven36645_8 adaptiveSpanWhole36645_8
        adaptiveSpanEvenEntries36645_8 adaptiveSpanWholeEntries36645_8
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanEvenDomain36645_8)
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanWholeDomain36645_8)
  · simpa only [adaptiveSpanLevel36645, adaptiveSpanNumerator36645, adaptiveSpanDenominator36645, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (9 : ℕ) ≠ 0 by decide), (show (9 : ℕ) ≠ 1 by decide), (show (9 : ℕ) ≠ 2 by decide), (show (9 : ℕ) ≠ 3 by decide), (show (9 : ℕ) ≠ 4 by decide), (show (9 : ℕ) ≠ 5 by decide), (show (9 : ℕ) ≠ 6 by decide), (show (9 : ℕ) ≠ 7 by decide), (show (9 : ℕ) ≠ 8 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 18323) (by decide : 0 < 1147)
        adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptiveSpanNumericCheck36645_9
        adaptiveSpanEven36645_9 adaptiveSpanWhole36645_9
        adaptiveSpanEvenEntries36645_9 adaptiveSpanWholeEntries36645_9
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanEvenDomain36645_9)
        (by rw [adaptiveSpanProfileLength36645]; exact adaptiveSpanWholeDomain36645_9)

/-- The complete finite histogram certificate for 33314 ≤ n ≤ 36645. -/
theorem adaptiveSpanHistogram36645 : DegreeIntervalCertificate 36645 adaptiveSpanPrimes36645
    (fun s v => sharpDegree (33314 / 2) 8 (adaptiveSpanNumerator36645 s)
      (adaptiveSpanDenominator36645 s) (totientDensity v))
    (fun s v => sharpDegree 33314 8 (adaptiveSpanNumerator36645 s)
      (adaptiveSpanDenominator36645 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows36645)
    adaptiveSpanPrimes36645
    (fun s => sharpDegree (33314 / 2) 8 (adaptiveSpanNumerator36645 s) (adaptiveSpanDenominator36645 s))
    (fun s => sharpDegree 33314 8 (adaptiveSpanNumerator36645 s) (adaptiveSpanDenominator36645 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid36645 adaptiveOrder36645 adaptivePermutationSemantics36645
    (by rw [adaptiveSpanProfileLength36645]; decide +kernel)
    adaptiveSpanLevel36645 adaptiveSpanTreeCache36645 adaptiveSpanTreeRepresents36645
    (fun j => adaptiveSpanWitness36645.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength36645
  · exact adaptiveSpanWitnessCheck36645

/-- Every required odd cycle for a dense set, throughout 33314 ≤ n ≤ 36645. -/
theorem adaptiveSpanInterval36645 {n : ℕ} (hLn : 33314 ≤ n) (hnU : n ≤ 36645)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes36645
    adaptiveSpanNumerator36645 adaptiveSpanDenominator36645 adaptiveSpanSharpTail36645
    adaptiveSpanPrimeSupport36645 adaptiveSpanHistogram36645 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail36645
#print axioms adaptiveSpanPrimeSupport36645
#print axioms adaptiveSpanHistogram36645
#print axioms adaptiveSpanInterval36645
end Erdos883Verified
