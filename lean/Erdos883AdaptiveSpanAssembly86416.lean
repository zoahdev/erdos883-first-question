import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate86416Metadata
import Erdos883AdaptiveSpan86416Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate86416PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes86416 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator86416 : ℕ → ℕ
  | 0 => 5760
  | 1 => 46080
  | 2 => 11520
  | 3 => 34560
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator86416 : ℕ → ℕ
  | 0 => 15015
  | 1 => 85085
  | 2 => 17017
  | 3 => 46189
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail86416 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes86416.length) :
    SharpTailCertificate 86416 (adaptiveSpanPrimes86416.take s)
      (adaptiveSpanNumerator86416 s) (adaptiveSpanDenominator86416 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 86416 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 86416 [3] 46080 85085
    refine ⟨by decide, {5, 7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 86416 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 86416 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 86416 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 86416 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 86416 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 86416 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 86416 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport86416 : ∀ u ∈ oddUniverse 86416,
    ∀ v ∈ oddUniverse 86416, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid86416 : AdaptiveProfileRowsValid adaptiveRows86416 :=
  coreProfileMetadataCheck_sound adaptiveMetadata86416

theorem adaptiveSpanProfileLength86416 : adaptiveRows86416.length = halfOdds 86416 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics86416
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache86416 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes86416.length) :
    (adaptiveSpanLevel86416 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel86416 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel86416, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache86416_0 adaptiveSpanWholeCache86416_0
  · simpa only [adaptiveSpanLevel86416, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache86416_1 adaptiveSpanWholeCache86416_1
  · simpa only [adaptiveSpanLevel86416, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache86416_2 adaptiveSpanWholeCache86416_2
  · simpa only [adaptiveSpanLevel86416, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache86416_3 adaptiveSpanWholeCache86416_3
  · simpa only [adaptiveSpanLevel86416, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache86416_4 adaptiveSpanWholeCache86416_4
  · simpa only [adaptiveSpanLevel86416, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache86416_5 adaptiveSpanWholeCache86416_5
  · simpa only [adaptiveSpanLevel86416, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache86416_6 adaptiveSpanWholeCache86416_6
  · simpa only [adaptiveSpanLevel86416, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache86416_7 adaptiveSpanWholeCache86416_7
  · simpa only [adaptiveSpanLevel86416, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache86416_8 adaptiveSpanWholeCache86416_8

theorem adaptiveSpanTreeRepresents86416 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes86416.length) :
    AdaptiveSpanTreeRepresents adaptiveRows86416 (halfOdds 86416)
      (sharpDegree (78560 / 2) 9 (adaptiveSpanNumerator86416 s) (adaptiveSpanDenominator86416 s))
      (sharpDegree 78560 9 (adaptiveSpanNumerator86416 s) (adaptiveSpanDenominator86416 s))
      (adaptiveSpanLevel86416 s).1 (adaptiveSpanLevel86416 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel86416, adaptiveSpanNumerator86416, adaptiveSpanDenominator86416, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 43208) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid86416 adaptiveOrder86416 adaptiveSpanNumericCheck86416_0
        adaptiveSpanEven86416_0 adaptiveSpanWhole86416_0
        adaptiveSpanEvenEntries86416_0 adaptiveSpanWholeEntries86416_0
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanEvenDomain86416_0)
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanWholeDomain86416_0)
  · simpa only [adaptiveSpanLevel86416, adaptiveSpanNumerator86416, adaptiveSpanDenominator86416, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 43208) (by decide : 0 < 85085)
        adaptiveSpanProfilesValid86416 adaptiveOrder86416 adaptiveSpanNumericCheck86416_1
        adaptiveSpanEven86416_1 adaptiveSpanWhole86416_1
        adaptiveSpanEvenEntries86416_1 adaptiveSpanWholeEntries86416_1
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanEvenDomain86416_1)
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanWholeDomain86416_1)
  · simpa only [adaptiveSpanLevel86416, adaptiveSpanNumerator86416, adaptiveSpanDenominator86416, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 43208) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid86416 adaptiveOrder86416 adaptiveSpanNumericCheck86416_2
        adaptiveSpanEven86416_2 adaptiveSpanWhole86416_2
        adaptiveSpanEvenEntries86416_2 adaptiveSpanWholeEntries86416_2
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanEvenDomain86416_2)
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanWholeDomain86416_2)
  · simpa only [adaptiveSpanLevel86416, adaptiveSpanNumerator86416, adaptiveSpanDenominator86416, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 43208) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid86416 adaptiveOrder86416 adaptiveSpanNumericCheck86416_3
        adaptiveSpanEven86416_3 adaptiveSpanWhole86416_3
        adaptiveSpanEvenEntries86416_3 adaptiveSpanWholeEntries86416_3
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanEvenDomain86416_3)
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanWholeDomain86416_3)
  · simpa only [adaptiveSpanLevel86416, adaptiveSpanNumerator86416, adaptiveSpanDenominator86416, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 43208) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid86416 adaptiveOrder86416 adaptiveSpanNumericCheck86416_4
        adaptiveSpanEven86416_4 adaptiveSpanWhole86416_4
        adaptiveSpanEvenEntries86416_4 adaptiveSpanWholeEntries86416_4
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanEvenDomain86416_4)
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanWholeDomain86416_4)
  · simpa only [adaptiveSpanLevel86416, adaptiveSpanNumerator86416, adaptiveSpanDenominator86416, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 43208) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid86416 adaptiveOrder86416 adaptiveSpanNumericCheck86416_5
        adaptiveSpanEven86416_5 adaptiveSpanWhole86416_5
        adaptiveSpanEvenEntries86416_5 adaptiveSpanWholeEntries86416_5
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanEvenDomain86416_5)
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanWholeDomain86416_5)
  · simpa only [adaptiveSpanLevel86416, adaptiveSpanNumerator86416, adaptiveSpanDenominator86416, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 43208) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid86416 adaptiveOrder86416 adaptiveSpanNumericCheck86416_6
        adaptiveSpanEven86416_6 adaptiveSpanWhole86416_6
        adaptiveSpanEvenEntries86416_6 adaptiveSpanWholeEntries86416_6
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanEvenDomain86416_6)
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanWholeDomain86416_6)
  · simpa only [adaptiveSpanLevel86416, adaptiveSpanNumerator86416, adaptiveSpanDenominator86416, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 43208) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid86416 adaptiveOrder86416 adaptiveSpanNumericCheck86416_7
        adaptiveSpanEven86416_7 adaptiveSpanWhole86416_7
        adaptiveSpanEvenEntries86416_7 adaptiveSpanWholeEntries86416_7
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanEvenDomain86416_7)
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanWholeDomain86416_7)
  · simpa only [adaptiveSpanLevel86416, adaptiveSpanNumerator86416, adaptiveSpanDenominator86416, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 43208) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid86416 adaptiveOrder86416 adaptiveSpanNumericCheck86416_8
        adaptiveSpanEven86416_8 adaptiveSpanWhole86416_8
        adaptiveSpanEvenEntries86416_8 adaptiveSpanWholeEntries86416_8
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanEvenDomain86416_8)
        (by rw [adaptiveSpanProfileLength86416]; exact adaptiveSpanWholeDomain86416_8)

/-- The complete finite histogram certificate for 78560 ≤ n ≤ 86416. -/
theorem adaptiveSpanHistogram86416 : DegreeIntervalCertificate 86416 adaptiveSpanPrimes86416
    (fun s v => sharpDegree (78560 / 2) 9 (adaptiveSpanNumerator86416 s)
      (adaptiveSpanDenominator86416 s) (totientDensity v))
    (fun s v => sharpDegree 78560 9 (adaptiveSpanNumerator86416 s)
      (adaptiveSpanDenominator86416 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows86416)
    adaptiveSpanPrimes86416
    (fun s => sharpDegree (78560 / 2) 9 (adaptiveSpanNumerator86416 s) (adaptiveSpanDenominator86416 s))
    (fun s => sharpDegree 78560 9 (adaptiveSpanNumerator86416 s) (adaptiveSpanDenominator86416 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid86416 adaptiveOrder86416 adaptivePermutationSemantics86416
    (by rw [adaptiveSpanProfileLength86416]; decide +kernel)
    adaptiveSpanLevel86416 adaptiveSpanTreeCache86416 adaptiveSpanTreeRepresents86416
    (fun j => adaptiveSpanWitness86416.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength86416
  · exact adaptiveSpanWitnessCheck86416

/-- Every required odd cycle for a dense set, throughout 78560 ≤ n ≤ 86416. -/
theorem adaptiveSpanInterval86416 {n : ℕ} (hLn : 78560 ≤ n) (hnU : n ≤ 86416)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes86416
    adaptiveSpanNumerator86416 adaptiveSpanDenominator86416 adaptiveSpanSharpTail86416
    adaptiveSpanPrimeSupport86416 adaptiveSpanHistogram86416 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail86416
#print axioms adaptiveSpanPrimeSupport86416
#print axioms adaptiveSpanHistogram86416
#print axioms adaptiveSpanInterval86416
end Erdos883Verified
