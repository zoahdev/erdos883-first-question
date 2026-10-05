import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate71417Metadata
import Erdos883AdaptiveSpan71417Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate71417PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes71417 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator71417 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 34560
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator71417 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 46189
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail71417 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes71417.length) :
    SharpTailCertificate 71417 (adaptiveSpanPrimes71417.take s)
      (adaptiveSpanNumerator71417 s) (adaptiveSpanDenominator71417 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 71417 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 71417 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 71417 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 71417 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 71417 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 71417 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 71417 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 71417 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 71417 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport71417 : ∀ u ∈ oddUniverse 71417,
    ∀ v ∈ oddUniverse 71417, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid71417 : AdaptiveProfileRowsValid adaptiveRows71417 :=
  coreProfileMetadataCheck_sound adaptiveMetadata71417

theorem adaptiveSpanProfileLength71417 : adaptiveRows71417.length = halfOdds 71417 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics71417
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache71417 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes71417.length) :
    (adaptiveSpanLevel71417 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel71417 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel71417, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache71417_0 adaptiveSpanWholeCache71417_0
  · simpa only [adaptiveSpanLevel71417, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache71417_1 adaptiveSpanWholeCache71417_1
  · simpa only [adaptiveSpanLevel71417, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache71417_2 adaptiveSpanWholeCache71417_2
  · simpa only [adaptiveSpanLevel71417, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache71417_3 adaptiveSpanWholeCache71417_3
  · simpa only [adaptiveSpanLevel71417, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache71417_4 adaptiveSpanWholeCache71417_4
  · simpa only [adaptiveSpanLevel71417, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache71417_5 adaptiveSpanWholeCache71417_5
  · simpa only [adaptiveSpanLevel71417, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache71417_6 adaptiveSpanWholeCache71417_6
  · simpa only [adaptiveSpanLevel71417, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache71417_7 adaptiveSpanWholeCache71417_7
  · simpa only [adaptiveSpanLevel71417, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache71417_8 adaptiveSpanWholeCache71417_8

theorem adaptiveSpanTreeRepresents71417 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes71417.length) :
    AdaptiveSpanTreeRepresents adaptiveRows71417 (halfOdds 71417)
      (sharpDegree (64925 / 2) 9 (adaptiveSpanNumerator71417 s) (adaptiveSpanDenominator71417 s))
      (sharpDegree 64925 9 (adaptiveSpanNumerator71417 s) (adaptiveSpanDenominator71417 s))
      (adaptiveSpanLevel71417 s).1 (adaptiveSpanLevel71417 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel71417, adaptiveSpanNumerator71417, adaptiveSpanDenominator71417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 35709) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid71417 adaptiveOrder71417 adaptiveSpanNumericCheck71417_0
        adaptiveSpanEven71417_0 adaptiveSpanWhole71417_0
        adaptiveSpanEvenEntries71417_0 adaptiveSpanWholeEntries71417_0
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanEvenDomain71417_0)
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanWholeDomain71417_0)
  · simpa only [adaptiveSpanLevel71417, adaptiveSpanNumerator71417, adaptiveSpanDenominator71417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 35709) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid71417 adaptiveOrder71417 adaptiveSpanNumericCheck71417_1
        adaptiveSpanEven71417_1 adaptiveSpanWhole71417_1
        adaptiveSpanEvenEntries71417_1 adaptiveSpanWholeEntries71417_1
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanEvenDomain71417_1)
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanWholeDomain71417_1)
  · simpa only [adaptiveSpanLevel71417, adaptiveSpanNumerator71417, adaptiveSpanDenominator71417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 35709) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid71417 adaptiveOrder71417 adaptiveSpanNumericCheck71417_2
        adaptiveSpanEven71417_2 adaptiveSpanWhole71417_2
        adaptiveSpanEvenEntries71417_2 adaptiveSpanWholeEntries71417_2
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanEvenDomain71417_2)
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanWholeDomain71417_2)
  · simpa only [adaptiveSpanLevel71417, adaptiveSpanNumerator71417, adaptiveSpanDenominator71417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 35709) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid71417 adaptiveOrder71417 adaptiveSpanNumericCheck71417_3
        adaptiveSpanEven71417_3 adaptiveSpanWhole71417_3
        adaptiveSpanEvenEntries71417_3 adaptiveSpanWholeEntries71417_3
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanEvenDomain71417_3)
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanWholeDomain71417_3)
  · simpa only [adaptiveSpanLevel71417, adaptiveSpanNumerator71417, adaptiveSpanDenominator71417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 35709) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid71417 adaptiveOrder71417 adaptiveSpanNumericCheck71417_4
        adaptiveSpanEven71417_4 adaptiveSpanWhole71417_4
        adaptiveSpanEvenEntries71417_4 adaptiveSpanWholeEntries71417_4
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanEvenDomain71417_4)
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanWholeDomain71417_4)
  · simpa only [adaptiveSpanLevel71417, adaptiveSpanNumerator71417, adaptiveSpanDenominator71417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 35709) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid71417 adaptiveOrder71417 adaptiveSpanNumericCheck71417_5
        adaptiveSpanEven71417_5 adaptiveSpanWhole71417_5
        adaptiveSpanEvenEntries71417_5 adaptiveSpanWholeEntries71417_5
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanEvenDomain71417_5)
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanWholeDomain71417_5)
  · simpa only [adaptiveSpanLevel71417, adaptiveSpanNumerator71417, adaptiveSpanDenominator71417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 35709) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid71417 adaptiveOrder71417 adaptiveSpanNumericCheck71417_6
        adaptiveSpanEven71417_6 adaptiveSpanWhole71417_6
        adaptiveSpanEvenEntries71417_6 adaptiveSpanWholeEntries71417_6
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanEvenDomain71417_6)
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanWholeDomain71417_6)
  · simpa only [adaptiveSpanLevel71417, adaptiveSpanNumerator71417, adaptiveSpanDenominator71417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 35709) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid71417 adaptiveOrder71417 adaptiveSpanNumericCheck71417_7
        adaptiveSpanEven71417_7 adaptiveSpanWhole71417_7
        adaptiveSpanEvenEntries71417_7 adaptiveSpanWholeEntries71417_7
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanEvenDomain71417_7)
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanWholeDomain71417_7)
  · simpa only [adaptiveSpanLevel71417, adaptiveSpanNumerator71417, adaptiveSpanDenominator71417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 35709) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid71417 adaptiveOrder71417 adaptiveSpanNumericCheck71417_8
        adaptiveSpanEven71417_8 adaptiveSpanWhole71417_8
        adaptiveSpanEvenEntries71417_8 adaptiveSpanWholeEntries71417_8
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanEvenDomain71417_8)
        (by rw [adaptiveSpanProfileLength71417]; exact adaptiveSpanWholeDomain71417_8)

/-- The complete finite histogram certificate for 64925 ≤ n ≤ 71417. -/
theorem adaptiveSpanHistogram71417 : DegreeIntervalCertificate 71417 adaptiveSpanPrimes71417
    (fun s v => sharpDegree (64925 / 2) 9 (adaptiveSpanNumerator71417 s)
      (adaptiveSpanDenominator71417 s) (totientDensity v))
    (fun s v => sharpDegree 64925 9 (adaptiveSpanNumerator71417 s)
      (adaptiveSpanDenominator71417 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows71417)
    adaptiveSpanPrimes71417
    (fun s => sharpDegree (64925 / 2) 9 (adaptiveSpanNumerator71417 s) (adaptiveSpanDenominator71417 s))
    (fun s => sharpDegree 64925 9 (adaptiveSpanNumerator71417 s) (adaptiveSpanDenominator71417 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid71417 adaptiveOrder71417 adaptivePermutationSemantics71417
    (by rw [adaptiveSpanProfileLength71417]; decide +kernel)
    adaptiveSpanLevel71417 adaptiveSpanTreeCache71417 adaptiveSpanTreeRepresents71417
    (fun j => adaptiveSpanWitness71417.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength71417
  · exact adaptiveSpanWitnessCheck71417

/-- Every required odd cycle for a dense set, throughout 64925 ≤ n ≤ 71417. -/
theorem adaptiveSpanInterval71417 {n : ℕ} (hLn : 64925 ≤ n) (hnU : n ≤ 71417)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes71417
    adaptiveSpanNumerator71417 adaptiveSpanDenominator71417 adaptiveSpanSharpTail71417
    adaptiveSpanPrimeSupport71417 adaptiveSpanHistogram71417 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail71417
#print axioms adaptiveSpanPrimeSupport71417
#print axioms adaptiveSpanHistogram71417
#print axioms adaptiveSpanInterval71417
end Erdos883Verified
