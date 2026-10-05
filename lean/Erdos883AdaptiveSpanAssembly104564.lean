import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate104564Metadata
import Erdos883AdaptiveSpan104564Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate104564PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes104564 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator104564 : ℕ → ℕ
  | 0 => 5760
  | 1 => 46080
  | 2 => 11520
  | 3 => 34560
  | 4 => 76032
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator104564 : ℕ → ℕ
  | 0 => 15015
  | 1 => 85085
  | 2 => 17017
  | 3 => 46189
  | 4 => 96577
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail104564 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes104564.length) :
    SharpTailCertificate 104564 (adaptiveSpanPrimes104564.take s)
      (adaptiveSpanNumerator104564 s) (adaptiveSpanDenominator104564 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 104564 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 104564 [3] 46080 85085
    refine ⟨by decide, {5, 7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 104564 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 104564 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 104564 [3, 5, 7, 11] 76032 96577
    refine ⟨by decide, {13, 17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 104564 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 104564 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 104564 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 104564 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport104564 : ∀ u ∈ oddUniverse 104564,
    ∀ v ∈ oddUniverse 104564, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid104564 : AdaptiveProfileRowsValid adaptiveRows104564 :=
  coreProfileMetadataCheck_sound adaptiveMetadata104564

theorem adaptiveSpanProfileLength104564 : adaptiveRows104564.length = halfOdds 104564 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics104564
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache104564 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes104564.length) :
    (adaptiveSpanLevel104564 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel104564 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel104564, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache104564_0 adaptiveSpanWholeCache104564_0
  · simpa only [adaptiveSpanLevel104564, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache104564_1 adaptiveSpanWholeCache104564_1
  · simpa only [adaptiveSpanLevel104564, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache104564_2 adaptiveSpanWholeCache104564_2
  · simpa only [adaptiveSpanLevel104564, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache104564_3 adaptiveSpanWholeCache104564_3
  · simpa only [adaptiveSpanLevel104564, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache104564_4 adaptiveSpanWholeCache104564_4
  · simpa only [adaptiveSpanLevel104564, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache104564_5 adaptiveSpanWholeCache104564_5
  · simpa only [adaptiveSpanLevel104564, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache104564_6 adaptiveSpanWholeCache104564_6
  · simpa only [adaptiveSpanLevel104564, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache104564_7 adaptiveSpanWholeCache104564_7
  · simpa only [adaptiveSpanLevel104564, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache104564_8 adaptiveSpanWholeCache104564_8

theorem adaptiveSpanTreeRepresents104564 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes104564.length) :
    AdaptiveSpanTreeRepresents adaptiveRows104564 (halfOdds 104564)
      (sharpDegree (95059 / 2) 9 (adaptiveSpanNumerator104564 s) (adaptiveSpanDenominator104564 s))
      (sharpDegree 95059 9 (adaptiveSpanNumerator104564 s) (adaptiveSpanDenominator104564 s))
      (adaptiveSpanLevel104564 s).1 (adaptiveSpanLevel104564 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel104564, adaptiveSpanNumerator104564, adaptiveSpanDenominator104564, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 52282) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid104564 adaptiveOrder104564 adaptiveSpanNumericCheck104564_0
        adaptiveSpanEven104564_0 adaptiveSpanWhole104564_0
        adaptiveSpanEvenEntries104564_0 adaptiveSpanWholeEntries104564_0
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanEvenDomain104564_0)
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanWholeDomain104564_0)
  · simpa only [adaptiveSpanLevel104564, adaptiveSpanNumerator104564, adaptiveSpanDenominator104564, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 52282) (by decide : 0 < 85085)
        adaptiveSpanProfilesValid104564 adaptiveOrder104564 adaptiveSpanNumericCheck104564_1
        adaptiveSpanEven104564_1 adaptiveSpanWhole104564_1
        adaptiveSpanEvenEntries104564_1 adaptiveSpanWholeEntries104564_1
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanEvenDomain104564_1)
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanWholeDomain104564_1)
  · simpa only [adaptiveSpanLevel104564, adaptiveSpanNumerator104564, adaptiveSpanDenominator104564, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 52282) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid104564 adaptiveOrder104564 adaptiveSpanNumericCheck104564_2
        adaptiveSpanEven104564_2 adaptiveSpanWhole104564_2
        adaptiveSpanEvenEntries104564_2 adaptiveSpanWholeEntries104564_2
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanEvenDomain104564_2)
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanWholeDomain104564_2)
  · simpa only [adaptiveSpanLevel104564, adaptiveSpanNumerator104564, adaptiveSpanDenominator104564, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 52282) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid104564 adaptiveOrder104564 adaptiveSpanNumericCheck104564_3
        adaptiveSpanEven104564_3 adaptiveSpanWhole104564_3
        adaptiveSpanEvenEntries104564_3 adaptiveSpanWholeEntries104564_3
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanEvenDomain104564_3)
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanWholeDomain104564_3)
  · simpa only [adaptiveSpanLevel104564, adaptiveSpanNumerator104564, adaptiveSpanDenominator104564, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 52282) (by decide : 0 < 96577)
        adaptiveSpanProfilesValid104564 adaptiveOrder104564 adaptiveSpanNumericCheck104564_4
        adaptiveSpanEven104564_4 adaptiveSpanWhole104564_4
        adaptiveSpanEvenEntries104564_4 adaptiveSpanWholeEntries104564_4
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanEvenDomain104564_4)
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanWholeDomain104564_4)
  · simpa only [adaptiveSpanLevel104564, adaptiveSpanNumerator104564, adaptiveSpanDenominator104564, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 52282) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid104564 adaptiveOrder104564 adaptiveSpanNumericCheck104564_5
        adaptiveSpanEven104564_5 adaptiveSpanWhole104564_5
        adaptiveSpanEvenEntries104564_5 adaptiveSpanWholeEntries104564_5
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanEvenDomain104564_5)
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanWholeDomain104564_5)
  · simpa only [adaptiveSpanLevel104564, adaptiveSpanNumerator104564, adaptiveSpanDenominator104564, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 52282) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid104564 adaptiveOrder104564 adaptiveSpanNumericCheck104564_6
        adaptiveSpanEven104564_6 adaptiveSpanWhole104564_6
        adaptiveSpanEvenEntries104564_6 adaptiveSpanWholeEntries104564_6
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanEvenDomain104564_6)
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanWholeDomain104564_6)
  · simpa only [adaptiveSpanLevel104564, adaptiveSpanNumerator104564, adaptiveSpanDenominator104564, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 52282) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid104564 adaptiveOrder104564 adaptiveSpanNumericCheck104564_7
        adaptiveSpanEven104564_7 adaptiveSpanWhole104564_7
        adaptiveSpanEvenEntries104564_7 adaptiveSpanWholeEntries104564_7
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanEvenDomain104564_7)
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanWholeDomain104564_7)
  · simpa only [adaptiveSpanLevel104564, adaptiveSpanNumerator104564, adaptiveSpanDenominator104564, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 52282) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid104564 adaptiveOrder104564 adaptiveSpanNumericCheck104564_8
        adaptiveSpanEven104564_8 adaptiveSpanWhole104564_8
        adaptiveSpanEvenEntries104564_8 adaptiveSpanWholeEntries104564_8
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanEvenDomain104564_8)
        (by rw [adaptiveSpanProfileLength104564]; exact adaptiveSpanWholeDomain104564_8)

/-- The complete finite histogram certificate for 95059 ≤ n ≤ 104564. -/
theorem adaptiveSpanHistogram104564 : DegreeIntervalCertificate 104564 adaptiveSpanPrimes104564
    (fun s v => sharpDegree (95059 / 2) 9 (adaptiveSpanNumerator104564 s)
      (adaptiveSpanDenominator104564 s) (totientDensity v))
    (fun s v => sharpDegree 95059 9 (adaptiveSpanNumerator104564 s)
      (adaptiveSpanDenominator104564 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows104564)
    adaptiveSpanPrimes104564
    (fun s => sharpDegree (95059 / 2) 9 (adaptiveSpanNumerator104564 s) (adaptiveSpanDenominator104564 s))
    (fun s => sharpDegree 95059 9 (adaptiveSpanNumerator104564 s) (adaptiveSpanDenominator104564 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid104564 adaptiveOrder104564 adaptivePermutationSemantics104564
    (by rw [adaptiveSpanProfileLength104564]; decide +kernel)
    adaptiveSpanLevel104564 adaptiveSpanTreeCache104564 adaptiveSpanTreeRepresents104564
    (fun j => adaptiveSpanWitness104564.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength104564
  · exact adaptiveSpanWitnessCheck104564

/-- Every required odd cycle for a dense set, throughout 95059 ≤ n ≤ 104564. -/
theorem adaptiveSpanInterval104564 {n : ℕ} (hLn : 95059 ≤ n) (hnU : n ≤ 104564)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes104564
    adaptiveSpanNumerator104564 adaptiveSpanDenominator104564 adaptiveSpanSharpTail104564
    adaptiveSpanPrimeSupport104564 adaptiveSpanHistogram104564 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail104564
#print axioms adaptiveSpanPrimeSupport104564
#print axioms adaptiveSpanHistogram104564
#print axioms adaptiveSpanInterval104564
end Erdos883Verified
