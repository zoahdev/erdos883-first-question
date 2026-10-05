import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate168405Metadata
import Erdos883AdaptiveSpan168405Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate168405PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes168405 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator168405 : ℕ → ℕ
  | 0 => 5760
  | 1 => 46080
  | 2 => 11520
  | 3 => 34560
  | 4 => 76032
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator168405 : ℕ → ℕ
  | 0 => 15015
  | 1 => 85085
  | 2 => 17017
  | 3 => 46189
  | 4 => 96577
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail168405 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes168405.length) :
    SharpTailCertificate 168405 (adaptiveSpanPrimes168405.take s)
      (adaptiveSpanNumerator168405 s) (adaptiveSpanDenominator168405 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 168405 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 168405 [3] 46080 85085
    refine ⟨by decide, {5, 7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 168405 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 168405 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 168405 [3, 5, 7, 11] 76032 96577
    refine ⟨by decide, {13, 17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 168405 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 168405 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 168405 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 168405 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport168405 : ∀ u ∈ oddUniverse 168405,
    ∀ v ∈ oddUniverse 168405, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid168405 : AdaptiveProfileRowsValid adaptiveRows168405 :=
  coreProfileMetadataCheck_sound adaptiveMetadata168405

theorem adaptiveSpanProfileLength168405 : adaptiveRows168405.length = halfOdds 168405 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics168405
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache168405 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes168405.length) :
    (adaptiveSpanLevel168405 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel168405 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel168405, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache168405_0 adaptiveSpanWholeCache168405_0
  · simpa only [adaptiveSpanLevel168405, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache168405_1 adaptiveSpanWholeCache168405_1
  · simpa only [adaptiveSpanLevel168405, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache168405_2 adaptiveSpanWholeCache168405_2
  · simpa only [adaptiveSpanLevel168405, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache168405_3 adaptiveSpanWholeCache168405_3
  · simpa only [adaptiveSpanLevel168405, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache168405_4 adaptiveSpanWholeCache168405_4
  · simpa only [adaptiveSpanLevel168405, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache168405_5 adaptiveSpanWholeCache168405_5
  · simpa only [adaptiveSpanLevel168405, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache168405_6 adaptiveSpanWholeCache168405_6
  · simpa only [adaptiveSpanLevel168405, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache168405_7 adaptiveSpanWholeCache168405_7
  · simpa only [adaptiveSpanLevel168405, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache168405_8 adaptiveSpanWholeCache168405_8

theorem adaptiveSpanTreeRepresents168405 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes168405.length) :
    AdaptiveSpanTreeRepresents adaptiveRows168405 (halfOdds 168405)
      (sharpDegree (153096 / 2) 9 (adaptiveSpanNumerator168405 s) (adaptiveSpanDenominator168405 s))
      (sharpDegree 153096 9 (adaptiveSpanNumerator168405 s) (adaptiveSpanDenominator168405 s))
      (adaptiveSpanLevel168405 s).1 (adaptiveSpanLevel168405 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel168405, adaptiveSpanNumerator168405, adaptiveSpanDenominator168405, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 84203) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid168405 adaptiveOrder168405 adaptiveSpanNumericCheck168405_0
        adaptiveSpanEven168405_0 adaptiveSpanWhole168405_0
        adaptiveSpanEvenEntries168405_0 adaptiveSpanWholeEntries168405_0
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanEvenDomain168405_0)
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanWholeDomain168405_0)
  · simpa only [adaptiveSpanLevel168405, adaptiveSpanNumerator168405, adaptiveSpanDenominator168405, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 84203) (by decide : 0 < 85085)
        adaptiveSpanProfilesValid168405 adaptiveOrder168405 adaptiveSpanNumericCheck168405_1
        adaptiveSpanEven168405_1 adaptiveSpanWhole168405_1
        adaptiveSpanEvenEntries168405_1 adaptiveSpanWholeEntries168405_1
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanEvenDomain168405_1)
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanWholeDomain168405_1)
  · simpa only [adaptiveSpanLevel168405, adaptiveSpanNumerator168405, adaptiveSpanDenominator168405, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 84203) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid168405 adaptiveOrder168405 adaptiveSpanNumericCheck168405_2
        adaptiveSpanEven168405_2 adaptiveSpanWhole168405_2
        adaptiveSpanEvenEntries168405_2 adaptiveSpanWholeEntries168405_2
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanEvenDomain168405_2)
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanWholeDomain168405_2)
  · simpa only [adaptiveSpanLevel168405, adaptiveSpanNumerator168405, adaptiveSpanDenominator168405, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 84203) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid168405 adaptiveOrder168405 adaptiveSpanNumericCheck168405_3
        adaptiveSpanEven168405_3 adaptiveSpanWhole168405_3
        adaptiveSpanEvenEntries168405_3 adaptiveSpanWholeEntries168405_3
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanEvenDomain168405_3)
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanWholeDomain168405_3)
  · simpa only [adaptiveSpanLevel168405, adaptiveSpanNumerator168405, adaptiveSpanDenominator168405, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 84203) (by decide : 0 < 96577)
        adaptiveSpanProfilesValid168405 adaptiveOrder168405 adaptiveSpanNumericCheck168405_4
        adaptiveSpanEven168405_4 adaptiveSpanWhole168405_4
        adaptiveSpanEvenEntries168405_4 adaptiveSpanWholeEntries168405_4
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanEvenDomain168405_4)
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanWholeDomain168405_4)
  · simpa only [adaptiveSpanLevel168405, adaptiveSpanNumerator168405, adaptiveSpanDenominator168405, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 84203) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid168405 adaptiveOrder168405 adaptiveSpanNumericCheck168405_5
        adaptiveSpanEven168405_5 adaptiveSpanWhole168405_5
        adaptiveSpanEvenEntries168405_5 adaptiveSpanWholeEntries168405_5
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanEvenDomain168405_5)
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanWholeDomain168405_5)
  · simpa only [adaptiveSpanLevel168405, adaptiveSpanNumerator168405, adaptiveSpanDenominator168405, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 84203) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid168405 adaptiveOrder168405 adaptiveSpanNumericCheck168405_6
        adaptiveSpanEven168405_6 adaptiveSpanWhole168405_6
        adaptiveSpanEvenEntries168405_6 adaptiveSpanWholeEntries168405_6
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanEvenDomain168405_6)
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanWholeDomain168405_6)
  · simpa only [adaptiveSpanLevel168405, adaptiveSpanNumerator168405, adaptiveSpanDenominator168405, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 84203) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid168405 adaptiveOrder168405 adaptiveSpanNumericCheck168405_7
        adaptiveSpanEven168405_7 adaptiveSpanWhole168405_7
        adaptiveSpanEvenEntries168405_7 adaptiveSpanWholeEntries168405_7
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanEvenDomain168405_7)
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanWholeDomain168405_7)
  · simpa only [adaptiveSpanLevel168405, adaptiveSpanNumerator168405, adaptiveSpanDenominator168405, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 84203) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid168405 adaptiveOrder168405 adaptiveSpanNumericCheck168405_8
        adaptiveSpanEven168405_8 adaptiveSpanWhole168405_8
        adaptiveSpanEvenEntries168405_8 adaptiveSpanWholeEntries168405_8
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanEvenDomain168405_8)
        (by rw [adaptiveSpanProfileLength168405]; exact adaptiveSpanWholeDomain168405_8)

/-- The complete finite histogram certificate for 153096 ≤ n ≤ 168405. -/
theorem adaptiveSpanHistogram168405 : DegreeIntervalCertificate 168405 adaptiveSpanPrimes168405
    (fun s v => sharpDegree (153096 / 2) 9 (adaptiveSpanNumerator168405 s)
      (adaptiveSpanDenominator168405 s) (totientDensity v))
    (fun s v => sharpDegree 153096 9 (adaptiveSpanNumerator168405 s)
      (adaptiveSpanDenominator168405 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows168405)
    adaptiveSpanPrimes168405
    (fun s => sharpDegree (153096 / 2) 9 (adaptiveSpanNumerator168405 s) (adaptiveSpanDenominator168405 s))
    (fun s => sharpDegree 153096 9 (adaptiveSpanNumerator168405 s) (adaptiveSpanDenominator168405 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid168405 adaptiveOrder168405 adaptivePermutationSemantics168405
    (by rw [adaptiveSpanProfileLength168405]; decide +kernel)
    adaptiveSpanLevel168405 adaptiveSpanTreeCache168405 adaptiveSpanTreeRepresents168405
    (fun j => adaptiveSpanWitness168405.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength168405
  · exact adaptiveSpanWitnessCheck168405

/-- Every required odd cycle for a dense set, throughout 153096 ≤ n ≤ 168405. -/
theorem adaptiveSpanInterval168405 {n : ℕ} (hLn : 153096 ≤ n) (hnU : n ≤ 168405)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes168405
    adaptiveSpanNumerator168405 adaptiveSpanDenominator168405 adaptiveSpanSharpTail168405
    adaptiveSpanPrimeSupport168405 adaptiveSpanHistogram168405 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail168405
#print axioms adaptiveSpanPrimeSupport168405
#print axioms adaptiveSpanHistogram168405
#print axioms adaptiveSpanInterval168405
end Erdos883Verified
