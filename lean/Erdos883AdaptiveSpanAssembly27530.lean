import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate27530Metadata
import Erdos883AdaptiveSpan27530Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate27530PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes27530 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator27530 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 840

def adaptiveSpanDenominator27530 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 899

theorem adaptiveSpanSharpTail27530 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes27530.length) :
    SharpTailCertificate 27530 (adaptiveSpanPrimes27530.take s)
      (adaptiveSpanNumerator27530 s) (adaptiveSpanDenominator27530 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 27530 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 27530 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 27530 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 27530 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 27530 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 27530 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 27530 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 27530 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 27530 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport27530 : ∀ u ∈ oddUniverse 27530,
    ∀ v ∈ oddUniverse 27530, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid27530 : AdaptiveProfileRowsValid adaptiveRows27530 :=
  coreProfileMetadataCheck_sound adaptiveMetadata27530

theorem adaptiveSpanProfileLength27530 : adaptiveRows27530.length = halfOdds 27530 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics27530
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache27530 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes27530.length) :
    (adaptiveSpanLevel27530 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel27530 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel27530, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache27530_0 adaptiveSpanWholeCache27530_0
  · simpa only [adaptiveSpanLevel27530, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache27530_1 adaptiveSpanWholeCache27530_1
  · simpa only [adaptiveSpanLevel27530, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache27530_2 adaptiveSpanWholeCache27530_2
  · simpa only [adaptiveSpanLevel27530, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache27530_3 adaptiveSpanWholeCache27530_3
  · simpa only [adaptiveSpanLevel27530, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache27530_4 adaptiveSpanWholeCache27530_4
  · simpa only [adaptiveSpanLevel27530, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache27530_5 adaptiveSpanWholeCache27530_5
  · simpa only [adaptiveSpanLevel27530, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache27530_6 adaptiveSpanWholeCache27530_6
  · simpa only [adaptiveSpanLevel27530, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache27530_7 adaptiveSpanWholeCache27530_7
  · simpa only [adaptiveSpanLevel27530, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache27530_8 adaptiveSpanWholeCache27530_8

theorem adaptiveSpanTreeRepresents27530 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes27530.length) :
    AdaptiveSpanTreeRepresents adaptiveRows27530 (halfOdds 27530)
      (sharpDegree (25028 / 2) 8 (adaptiveSpanNumerator27530 s) (adaptiveSpanDenominator27530 s))
      (sharpDegree 25028 8 (adaptiveSpanNumerator27530 s) (adaptiveSpanDenominator27530 s))
      (adaptiveSpanLevel27530 s).1 (adaptiveSpanLevel27530 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel27530, adaptiveSpanNumerator27530, adaptiveSpanDenominator27530, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 13765) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid27530 adaptiveOrder27530 adaptiveSpanNumericCheck27530_0
        adaptiveSpanEven27530_0 adaptiveSpanWhole27530_0
        adaptiveSpanEvenEntries27530_0 adaptiveSpanWholeEntries27530_0
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanEvenDomain27530_0)
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanWholeDomain27530_0)
  · simpa only [adaptiveSpanLevel27530, adaptiveSpanNumerator27530, adaptiveSpanDenominator27530, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 13765) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid27530 adaptiveOrder27530 adaptiveSpanNumericCheck27530_1
        adaptiveSpanEven27530_1 adaptiveSpanWhole27530_1
        adaptiveSpanEvenEntries27530_1 adaptiveSpanWholeEntries27530_1
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanEvenDomain27530_1)
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanWholeDomain27530_1)
  · simpa only [adaptiveSpanLevel27530, adaptiveSpanNumerator27530, adaptiveSpanDenominator27530, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 13765) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid27530 adaptiveOrder27530 adaptiveSpanNumericCheck27530_2
        adaptiveSpanEven27530_2 adaptiveSpanWhole27530_2
        adaptiveSpanEvenEntries27530_2 adaptiveSpanWholeEntries27530_2
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanEvenDomain27530_2)
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanWholeDomain27530_2)
  · simpa only [adaptiveSpanLevel27530, adaptiveSpanNumerator27530, adaptiveSpanDenominator27530, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 13765) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid27530 adaptiveOrder27530 adaptiveSpanNumericCheck27530_3
        adaptiveSpanEven27530_3 adaptiveSpanWhole27530_3
        adaptiveSpanEvenEntries27530_3 adaptiveSpanWholeEntries27530_3
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanEvenDomain27530_3)
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanWholeDomain27530_3)
  · simpa only [adaptiveSpanLevel27530, adaptiveSpanNumerator27530, adaptiveSpanDenominator27530, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 13765) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid27530 adaptiveOrder27530 adaptiveSpanNumericCheck27530_4
        adaptiveSpanEven27530_4 adaptiveSpanWhole27530_4
        adaptiveSpanEvenEntries27530_4 adaptiveSpanWholeEntries27530_4
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanEvenDomain27530_4)
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanWholeDomain27530_4)
  · simpa only [adaptiveSpanLevel27530, adaptiveSpanNumerator27530, adaptiveSpanDenominator27530, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 13765) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid27530 adaptiveOrder27530 adaptiveSpanNumericCheck27530_5
        adaptiveSpanEven27530_5 adaptiveSpanWhole27530_5
        adaptiveSpanEvenEntries27530_5 adaptiveSpanWholeEntries27530_5
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanEvenDomain27530_5)
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanWholeDomain27530_5)
  · simpa only [adaptiveSpanLevel27530, adaptiveSpanNumerator27530, adaptiveSpanDenominator27530, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 13765) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid27530 adaptiveOrder27530 adaptiveSpanNumericCheck27530_6
        adaptiveSpanEven27530_6 adaptiveSpanWhole27530_6
        adaptiveSpanEvenEntries27530_6 adaptiveSpanWholeEntries27530_6
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanEvenDomain27530_6)
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanWholeDomain27530_6)
  · simpa only [adaptiveSpanLevel27530, adaptiveSpanNumerator27530, adaptiveSpanDenominator27530, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 13765) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid27530 adaptiveOrder27530 adaptiveSpanNumericCheck27530_7
        adaptiveSpanEven27530_7 adaptiveSpanWhole27530_7
        adaptiveSpanEvenEntries27530_7 adaptiveSpanWholeEntries27530_7
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanEvenDomain27530_7)
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanWholeDomain27530_7)
  · simpa only [adaptiveSpanLevel27530, adaptiveSpanNumerator27530, adaptiveSpanDenominator27530, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 13765) (by decide : 0 < 899)
        adaptiveSpanProfilesValid27530 adaptiveOrder27530 adaptiveSpanNumericCheck27530_8
        adaptiveSpanEven27530_8 adaptiveSpanWhole27530_8
        adaptiveSpanEvenEntries27530_8 adaptiveSpanWholeEntries27530_8
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanEvenDomain27530_8)
        (by rw [adaptiveSpanProfileLength27530]; exact adaptiveSpanWholeDomain27530_8)

/-- The complete finite histogram certificate for 25028 ≤ n ≤ 27530. -/
theorem adaptiveSpanHistogram27530 : DegreeIntervalCertificate 27530 adaptiveSpanPrimes27530
    (fun s v => sharpDegree (25028 / 2) 8 (adaptiveSpanNumerator27530 s)
      (adaptiveSpanDenominator27530 s) (totientDensity v))
    (fun s v => sharpDegree 25028 8 (adaptiveSpanNumerator27530 s)
      (adaptiveSpanDenominator27530 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows27530)
    adaptiveSpanPrimes27530
    (fun s => sharpDegree (25028 / 2) 8 (adaptiveSpanNumerator27530 s) (adaptiveSpanDenominator27530 s))
    (fun s => sharpDegree 25028 8 (adaptiveSpanNumerator27530 s) (adaptiveSpanDenominator27530 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid27530 adaptiveOrder27530 adaptivePermutationSemantics27530
    (by rw [adaptiveSpanProfileLength27530]; decide +kernel)
    adaptiveSpanLevel27530 adaptiveSpanTreeCache27530 adaptiveSpanTreeRepresents27530
    (fun j => adaptiveSpanWitness27530.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength27530
  · exact adaptiveSpanWitnessCheck27530

/-- Every required odd cycle for a dense set, throughout 25028 ≤ n ≤ 27530. -/
theorem adaptiveSpanInterval27530 {n : ℕ} (hLn : 25028 ≤ n) (hnU : n ≤ 27530)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes27530
    adaptiveSpanNumerator27530 adaptiveSpanDenominator27530 adaptiveSpanSharpTail27530
    adaptiveSpanPrimeSupport27530 adaptiveSpanHistogram27530 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail27530
#print axioms adaptiveSpanPrimeSupport27530
#print axioms adaptiveSpanHistogram27530
#print axioms adaptiveSpanInterval27530
end Erdos883Verified
