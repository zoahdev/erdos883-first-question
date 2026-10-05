import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate78559Metadata
import Erdos883AdaptiveSpan78559Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate78559PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes78559 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator78559 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 34560
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator78559 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 46189
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail78559 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes78559.length) :
    SharpTailCertificate 78559 (adaptiveSpanPrimes78559.take s)
      (adaptiveSpanNumerator78559 s) (adaptiveSpanDenominator78559 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 78559 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 78559 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 78559 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 78559 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 78559 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 78559 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 78559 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 78559 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 78559 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport78559 : ∀ u ∈ oddUniverse 78559,
    ∀ v ∈ oddUniverse 78559, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid78559 : AdaptiveProfileRowsValid adaptiveRows78559 :=
  coreProfileMetadataCheck_sound adaptiveMetadata78559

theorem adaptiveSpanProfileLength78559 : adaptiveRows78559.length = halfOdds 78559 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics78559
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache78559 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes78559.length) :
    (adaptiveSpanLevel78559 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel78559 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel78559, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache78559_0 adaptiveSpanWholeCache78559_0
  · simpa only [adaptiveSpanLevel78559, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache78559_1 adaptiveSpanWholeCache78559_1
  · simpa only [adaptiveSpanLevel78559, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache78559_2 adaptiveSpanWholeCache78559_2
  · simpa only [adaptiveSpanLevel78559, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache78559_3 adaptiveSpanWholeCache78559_3
  · simpa only [adaptiveSpanLevel78559, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache78559_4 adaptiveSpanWholeCache78559_4
  · simpa only [adaptiveSpanLevel78559, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache78559_5 adaptiveSpanWholeCache78559_5
  · simpa only [adaptiveSpanLevel78559, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache78559_6 adaptiveSpanWholeCache78559_6
  · simpa only [adaptiveSpanLevel78559, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache78559_7 adaptiveSpanWholeCache78559_7
  · simpa only [adaptiveSpanLevel78559, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache78559_8 adaptiveSpanWholeCache78559_8

theorem adaptiveSpanTreeRepresents78559 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes78559.length) :
    AdaptiveSpanTreeRepresents adaptiveRows78559 (halfOdds 78559)
      (sharpDegree (71418 / 2) 9 (adaptiveSpanNumerator78559 s) (adaptiveSpanDenominator78559 s))
      (sharpDegree 71418 9 (adaptiveSpanNumerator78559 s) (adaptiveSpanDenominator78559 s))
      (adaptiveSpanLevel78559 s).1 (adaptiveSpanLevel78559 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel78559, adaptiveSpanNumerator78559, adaptiveSpanDenominator78559, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 39280) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid78559 adaptiveOrder78559 adaptiveSpanNumericCheck78559_0
        adaptiveSpanEven78559_0 adaptiveSpanWhole78559_0
        adaptiveSpanEvenEntries78559_0 adaptiveSpanWholeEntries78559_0
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanEvenDomain78559_0)
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanWholeDomain78559_0)
  · simpa only [adaptiveSpanLevel78559, adaptiveSpanNumerator78559, adaptiveSpanDenominator78559, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 39280) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid78559 adaptiveOrder78559 adaptiveSpanNumericCheck78559_1
        adaptiveSpanEven78559_1 adaptiveSpanWhole78559_1
        adaptiveSpanEvenEntries78559_1 adaptiveSpanWholeEntries78559_1
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanEvenDomain78559_1)
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanWholeDomain78559_1)
  · simpa only [adaptiveSpanLevel78559, adaptiveSpanNumerator78559, adaptiveSpanDenominator78559, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 39280) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid78559 adaptiveOrder78559 adaptiveSpanNumericCheck78559_2
        adaptiveSpanEven78559_2 adaptiveSpanWhole78559_2
        adaptiveSpanEvenEntries78559_2 adaptiveSpanWholeEntries78559_2
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanEvenDomain78559_2)
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanWholeDomain78559_2)
  · simpa only [adaptiveSpanLevel78559, adaptiveSpanNumerator78559, adaptiveSpanDenominator78559, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 39280) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid78559 adaptiveOrder78559 adaptiveSpanNumericCheck78559_3
        adaptiveSpanEven78559_3 adaptiveSpanWhole78559_3
        adaptiveSpanEvenEntries78559_3 adaptiveSpanWholeEntries78559_3
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanEvenDomain78559_3)
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanWholeDomain78559_3)
  · simpa only [adaptiveSpanLevel78559, adaptiveSpanNumerator78559, adaptiveSpanDenominator78559, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 39280) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid78559 adaptiveOrder78559 adaptiveSpanNumericCheck78559_4
        adaptiveSpanEven78559_4 adaptiveSpanWhole78559_4
        adaptiveSpanEvenEntries78559_4 adaptiveSpanWholeEntries78559_4
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanEvenDomain78559_4)
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanWholeDomain78559_4)
  · simpa only [adaptiveSpanLevel78559, adaptiveSpanNumerator78559, adaptiveSpanDenominator78559, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 39280) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid78559 adaptiveOrder78559 adaptiveSpanNumericCheck78559_5
        adaptiveSpanEven78559_5 adaptiveSpanWhole78559_5
        adaptiveSpanEvenEntries78559_5 adaptiveSpanWholeEntries78559_5
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanEvenDomain78559_5)
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanWholeDomain78559_5)
  · simpa only [adaptiveSpanLevel78559, adaptiveSpanNumerator78559, adaptiveSpanDenominator78559, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 39280) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid78559 adaptiveOrder78559 adaptiveSpanNumericCheck78559_6
        adaptiveSpanEven78559_6 adaptiveSpanWhole78559_6
        adaptiveSpanEvenEntries78559_6 adaptiveSpanWholeEntries78559_6
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanEvenDomain78559_6)
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanWholeDomain78559_6)
  · simpa only [adaptiveSpanLevel78559, adaptiveSpanNumerator78559, adaptiveSpanDenominator78559, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 39280) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid78559 adaptiveOrder78559 adaptiveSpanNumericCheck78559_7
        adaptiveSpanEven78559_7 adaptiveSpanWhole78559_7
        adaptiveSpanEvenEntries78559_7 adaptiveSpanWholeEntries78559_7
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanEvenDomain78559_7)
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanWholeDomain78559_7)
  · simpa only [adaptiveSpanLevel78559, adaptiveSpanNumerator78559, adaptiveSpanDenominator78559, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 39280) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid78559 adaptiveOrder78559 adaptiveSpanNumericCheck78559_8
        adaptiveSpanEven78559_8 adaptiveSpanWhole78559_8
        adaptiveSpanEvenEntries78559_8 adaptiveSpanWholeEntries78559_8
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanEvenDomain78559_8)
        (by rw [adaptiveSpanProfileLength78559]; exact adaptiveSpanWholeDomain78559_8)

/-- The complete finite histogram certificate for 71418 ≤ n ≤ 78559. -/
theorem adaptiveSpanHistogram78559 : DegreeIntervalCertificate 78559 adaptiveSpanPrimes78559
    (fun s v => sharpDegree (71418 / 2) 9 (adaptiveSpanNumerator78559 s)
      (adaptiveSpanDenominator78559 s) (totientDensity v))
    (fun s v => sharpDegree 71418 9 (adaptiveSpanNumerator78559 s)
      (adaptiveSpanDenominator78559 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows78559)
    adaptiveSpanPrimes78559
    (fun s => sharpDegree (71418 / 2) 9 (adaptiveSpanNumerator78559 s) (adaptiveSpanDenominator78559 s))
    (fun s => sharpDegree 71418 9 (adaptiveSpanNumerator78559 s) (adaptiveSpanDenominator78559 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid78559 adaptiveOrder78559 adaptivePermutationSemantics78559
    (by rw [adaptiveSpanProfileLength78559]; decide +kernel)
    adaptiveSpanLevel78559 adaptiveSpanTreeCache78559 adaptiveSpanTreeRepresents78559
    (fun j => adaptiveSpanWitness78559.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength78559
  · exact adaptiveSpanWitnessCheck78559

/-- Every required odd cycle for a dense set, throughout 71418 ≤ n ≤ 78559. -/
theorem adaptiveSpanInterval78559 {n : ℕ} (hLn : 71418 ≤ n) (hnU : n ≤ 78559)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes78559
    adaptiveSpanNumerator78559 adaptiveSpanDenominator78559 adaptiveSpanSharpTail78559
    adaptiveSpanPrimeSupport78559 adaptiveSpanHistogram78559 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail78559
#print axioms adaptiveSpanPrimeSupport78559
#print axioms adaptiveSpanHistogram78559
#print axioms adaptiveSpanInterval78559
end Erdos883Verified
