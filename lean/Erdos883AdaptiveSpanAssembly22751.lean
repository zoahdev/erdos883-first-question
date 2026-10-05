import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate22751Metadata
import Erdos883AdaptiveSpan22751Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate22751PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes22751 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator22751 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 840

def adaptiveSpanDenominator22751 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 899

theorem adaptiveSpanSharpTail22751 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes22751.length) :
    SharpTailCertificate 22751 (adaptiveSpanPrimes22751.take s)
      (adaptiveSpanNumerator22751 s) (adaptiveSpanDenominator22751 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 22751 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 22751 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 22751 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 22751 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 22751 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 22751 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 22751 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 22751 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 22751 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport22751 : ∀ u ∈ oddUniverse 22751,
    ∀ v ∈ oddUniverse 22751, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid22751 : AdaptiveProfileRowsValid adaptiveRows22751 :=
  coreProfileMetadataCheck_sound adaptiveMetadata22751

theorem adaptiveSpanProfileLength22751 : adaptiveRows22751.length = halfOdds 22751 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics22751
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache22751 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes22751.length) :
    (adaptiveSpanLevel22751 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel22751 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel22751, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache22751_0 adaptiveSpanWholeCache22751_0
  · simpa only [adaptiveSpanLevel22751, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache22751_1 adaptiveSpanWholeCache22751_1
  · simpa only [adaptiveSpanLevel22751, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache22751_2 adaptiveSpanWholeCache22751_2
  · simpa only [adaptiveSpanLevel22751, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache22751_3 adaptiveSpanWholeCache22751_3
  · simpa only [adaptiveSpanLevel22751, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache22751_4 adaptiveSpanWholeCache22751_4
  · simpa only [adaptiveSpanLevel22751, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache22751_5 adaptiveSpanWholeCache22751_5
  · simpa only [adaptiveSpanLevel22751, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache22751_6 adaptiveSpanWholeCache22751_6
  · simpa only [adaptiveSpanLevel22751, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache22751_7 adaptiveSpanWholeCache22751_7
  · simpa only [adaptiveSpanLevel22751, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache22751_8 adaptiveSpanWholeCache22751_8

theorem adaptiveSpanTreeRepresents22751 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes22751.length) :
    AdaptiveSpanTreeRepresents adaptiveRows22751 (halfOdds 22751)
      (sharpDegree (20683 / 2) 8 (adaptiveSpanNumerator22751 s) (adaptiveSpanDenominator22751 s))
      (sharpDegree 20683 8 (adaptiveSpanNumerator22751 s) (adaptiveSpanDenominator22751 s))
      (adaptiveSpanLevel22751 s).1 (adaptiveSpanLevel22751 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel22751, adaptiveSpanNumerator22751, adaptiveSpanDenominator22751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 11376) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid22751 adaptiveOrder22751 adaptiveSpanNumericCheck22751_0
        adaptiveSpanEven22751_0 adaptiveSpanWhole22751_0
        adaptiveSpanEvenEntries22751_0 adaptiveSpanWholeEntries22751_0
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanEvenDomain22751_0)
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanWholeDomain22751_0)
  · simpa only [adaptiveSpanLevel22751, adaptiveSpanNumerator22751, adaptiveSpanDenominator22751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 11376) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid22751 adaptiveOrder22751 adaptiveSpanNumericCheck22751_1
        adaptiveSpanEven22751_1 adaptiveSpanWhole22751_1
        adaptiveSpanEvenEntries22751_1 adaptiveSpanWholeEntries22751_1
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanEvenDomain22751_1)
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanWholeDomain22751_1)
  · simpa only [adaptiveSpanLevel22751, adaptiveSpanNumerator22751, adaptiveSpanDenominator22751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 11376) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid22751 adaptiveOrder22751 adaptiveSpanNumericCheck22751_2
        adaptiveSpanEven22751_2 adaptiveSpanWhole22751_2
        adaptiveSpanEvenEntries22751_2 adaptiveSpanWholeEntries22751_2
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanEvenDomain22751_2)
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanWholeDomain22751_2)
  · simpa only [adaptiveSpanLevel22751, adaptiveSpanNumerator22751, adaptiveSpanDenominator22751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 11376) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid22751 adaptiveOrder22751 adaptiveSpanNumericCheck22751_3
        adaptiveSpanEven22751_3 adaptiveSpanWhole22751_3
        adaptiveSpanEvenEntries22751_3 adaptiveSpanWholeEntries22751_3
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanEvenDomain22751_3)
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanWholeDomain22751_3)
  · simpa only [adaptiveSpanLevel22751, adaptiveSpanNumerator22751, adaptiveSpanDenominator22751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 11376) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid22751 adaptiveOrder22751 adaptiveSpanNumericCheck22751_4
        adaptiveSpanEven22751_4 adaptiveSpanWhole22751_4
        adaptiveSpanEvenEntries22751_4 adaptiveSpanWholeEntries22751_4
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanEvenDomain22751_4)
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanWholeDomain22751_4)
  · simpa only [adaptiveSpanLevel22751, adaptiveSpanNumerator22751, adaptiveSpanDenominator22751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 11376) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid22751 adaptiveOrder22751 adaptiveSpanNumericCheck22751_5
        adaptiveSpanEven22751_5 adaptiveSpanWhole22751_5
        adaptiveSpanEvenEntries22751_5 adaptiveSpanWholeEntries22751_5
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanEvenDomain22751_5)
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanWholeDomain22751_5)
  · simpa only [adaptiveSpanLevel22751, adaptiveSpanNumerator22751, adaptiveSpanDenominator22751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 11376) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid22751 adaptiveOrder22751 adaptiveSpanNumericCheck22751_6
        adaptiveSpanEven22751_6 adaptiveSpanWhole22751_6
        adaptiveSpanEvenEntries22751_6 adaptiveSpanWholeEntries22751_6
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanEvenDomain22751_6)
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanWholeDomain22751_6)
  · simpa only [adaptiveSpanLevel22751, adaptiveSpanNumerator22751, adaptiveSpanDenominator22751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 11376) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid22751 adaptiveOrder22751 adaptiveSpanNumericCheck22751_7
        adaptiveSpanEven22751_7 adaptiveSpanWhole22751_7
        adaptiveSpanEvenEntries22751_7 adaptiveSpanWholeEntries22751_7
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanEvenDomain22751_7)
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanWholeDomain22751_7)
  · simpa only [adaptiveSpanLevel22751, adaptiveSpanNumerator22751, adaptiveSpanDenominator22751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 11376) (by decide : 0 < 899)
        adaptiveSpanProfilesValid22751 adaptiveOrder22751 adaptiveSpanNumericCheck22751_8
        adaptiveSpanEven22751_8 adaptiveSpanWhole22751_8
        adaptiveSpanEvenEntries22751_8 adaptiveSpanWholeEntries22751_8
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanEvenDomain22751_8)
        (by rw [adaptiveSpanProfileLength22751]; exact adaptiveSpanWholeDomain22751_8)

/-- The complete finite histogram certificate for 20683 ≤ n ≤ 22751. -/
theorem adaptiveSpanHistogram22751 : DegreeIntervalCertificate 22751 adaptiveSpanPrimes22751
    (fun s v => sharpDegree (20683 / 2) 8 (adaptiveSpanNumerator22751 s)
      (adaptiveSpanDenominator22751 s) (totientDensity v))
    (fun s v => sharpDegree 20683 8 (adaptiveSpanNumerator22751 s)
      (adaptiveSpanDenominator22751 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows22751)
    adaptiveSpanPrimes22751
    (fun s => sharpDegree (20683 / 2) 8 (adaptiveSpanNumerator22751 s) (adaptiveSpanDenominator22751 s))
    (fun s => sharpDegree 20683 8 (adaptiveSpanNumerator22751 s) (adaptiveSpanDenominator22751 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid22751 adaptiveOrder22751 adaptivePermutationSemantics22751
    (by rw [adaptiveSpanProfileLength22751]; decide +kernel)
    adaptiveSpanLevel22751 adaptiveSpanTreeCache22751 adaptiveSpanTreeRepresents22751
    (fun j => adaptiveSpanWitness22751.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength22751
  · exact adaptiveSpanWitnessCheck22751

/-- Every required odd cycle for a dense set, throughout 20683 ≤ n ≤ 22751. -/
theorem adaptiveSpanInterval22751 {n : ℕ} (hLn : 20683 ≤ n) (hnU : n ≤ 22751)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes22751
    adaptiveSpanNumerator22751 adaptiveSpanDenominator22751 adaptiveSpanSharpTail22751
    adaptiveSpanPrimeSupport22751 adaptiveSpanHistogram22751 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail22751
#print axioms adaptiveSpanPrimeSupport22751
#print axioms adaptiveSpanHistogram22751
#print axioms adaptiveSpanInterval22751
end Erdos883Verified
