import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate12839Metadata
import Erdos883AdaptiveSpan12839Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate12839PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes12839 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator12839 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator12839 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail12839 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes12839.length) :
    SharpTailCertificate 12839 (adaptiveSpanPrimes12839.take s)
      (adaptiveSpanNumerator12839 s) (adaptiveSpanDenominator12839 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 12839 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 12839 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 12839 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 12839 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 12839 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 12839 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 12839 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 12839 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 12839 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport12839 : ∀ u ∈ oddUniverse 12839,
    ∀ v ∈ oddUniverse 12839, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid12839 : AdaptiveProfileRowsValid adaptiveRows12839 :=
  coreProfileMetadataCheck_sound adaptiveMetadata12839

theorem adaptiveSpanProfileLength12839 : adaptiveRows12839.length = halfOdds 12839 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics12839
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache12839 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes12839.length) :
    (adaptiveSpanLevel12839 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel12839 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel12839, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache12839_0 adaptiveSpanWholeCache12839_0
  · simpa only [adaptiveSpanLevel12839, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache12839_1 adaptiveSpanWholeCache12839_1
  · simpa only [adaptiveSpanLevel12839, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache12839_2 adaptiveSpanWholeCache12839_2
  · simpa only [adaptiveSpanLevel12839, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache12839_3 adaptiveSpanWholeCache12839_3
  · simpa only [adaptiveSpanLevel12839, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache12839_4 adaptiveSpanWholeCache12839_4
  · simpa only [adaptiveSpanLevel12839, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache12839_5 adaptiveSpanWholeCache12839_5
  · simpa only [adaptiveSpanLevel12839, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache12839_6 adaptiveSpanWholeCache12839_6
  · simpa only [adaptiveSpanLevel12839, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache12839_7 adaptiveSpanWholeCache12839_7
  · simpa only [adaptiveSpanLevel12839, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache12839_8 adaptiveSpanWholeCache12839_8

theorem adaptiveSpanTreeRepresents12839 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes12839.length) :
    AdaptiveSpanTreeRepresents adaptiveRows12839 (halfOdds 12839)
      (sharpDegree (11672 / 2) 8 (adaptiveSpanNumerator12839 s) (adaptiveSpanDenominator12839 s))
      (sharpDegree 11672 8 (adaptiveSpanNumerator12839 s) (adaptiveSpanDenominator12839 s))
      (adaptiveSpanLevel12839 s).1 (adaptiveSpanLevel12839 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel12839, adaptiveSpanNumerator12839, adaptiveSpanDenominator12839, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 6420) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid12839 adaptiveOrder12839 adaptiveSpanNumericCheck12839_0
        adaptiveSpanEven12839_0 adaptiveSpanWhole12839_0
        adaptiveSpanEvenEntries12839_0 adaptiveSpanWholeEntries12839_0
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanEvenDomain12839_0)
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanWholeDomain12839_0)
  · simpa only [adaptiveSpanLevel12839, adaptiveSpanNumerator12839, adaptiveSpanDenominator12839, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 6420) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid12839 adaptiveOrder12839 adaptiveSpanNumericCheck12839_1
        adaptiveSpanEven12839_1 adaptiveSpanWhole12839_1
        adaptiveSpanEvenEntries12839_1 adaptiveSpanWholeEntries12839_1
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanEvenDomain12839_1)
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanWholeDomain12839_1)
  · simpa only [adaptiveSpanLevel12839, adaptiveSpanNumerator12839, adaptiveSpanDenominator12839, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 6420) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid12839 adaptiveOrder12839 adaptiveSpanNumericCheck12839_2
        adaptiveSpanEven12839_2 adaptiveSpanWhole12839_2
        adaptiveSpanEvenEntries12839_2 adaptiveSpanWholeEntries12839_2
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanEvenDomain12839_2)
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanWholeDomain12839_2)
  · simpa only [adaptiveSpanLevel12839, adaptiveSpanNumerator12839, adaptiveSpanDenominator12839, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 6420) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid12839 adaptiveOrder12839 adaptiveSpanNumericCheck12839_3
        adaptiveSpanEven12839_3 adaptiveSpanWhole12839_3
        adaptiveSpanEvenEntries12839_3 adaptiveSpanWholeEntries12839_3
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanEvenDomain12839_3)
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanWholeDomain12839_3)
  · simpa only [adaptiveSpanLevel12839, adaptiveSpanNumerator12839, adaptiveSpanDenominator12839, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 6420) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid12839 adaptiveOrder12839 adaptiveSpanNumericCheck12839_4
        adaptiveSpanEven12839_4 adaptiveSpanWhole12839_4
        adaptiveSpanEvenEntries12839_4 adaptiveSpanWholeEntries12839_4
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanEvenDomain12839_4)
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanWholeDomain12839_4)
  · simpa only [adaptiveSpanLevel12839, adaptiveSpanNumerator12839, adaptiveSpanDenominator12839, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 6420) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid12839 adaptiveOrder12839 adaptiveSpanNumericCheck12839_5
        adaptiveSpanEven12839_5 adaptiveSpanWhole12839_5
        adaptiveSpanEvenEntries12839_5 adaptiveSpanWholeEntries12839_5
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanEvenDomain12839_5)
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanWholeDomain12839_5)
  · simpa only [adaptiveSpanLevel12839, adaptiveSpanNumerator12839, adaptiveSpanDenominator12839, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 6420) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid12839 adaptiveOrder12839 adaptiveSpanNumericCheck12839_6
        adaptiveSpanEven12839_6 adaptiveSpanWhole12839_6
        adaptiveSpanEvenEntries12839_6 adaptiveSpanWholeEntries12839_6
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanEvenDomain12839_6)
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanWholeDomain12839_6)
  · simpa only [adaptiveSpanLevel12839, adaptiveSpanNumerator12839, adaptiveSpanDenominator12839, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 6420) (by decide : 0 < 667)
        adaptiveSpanProfilesValid12839 adaptiveOrder12839 adaptiveSpanNumericCheck12839_7
        adaptiveSpanEven12839_7 adaptiveSpanWhole12839_7
        adaptiveSpanEvenEntries12839_7 adaptiveSpanWholeEntries12839_7
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanEvenDomain12839_7)
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanWholeDomain12839_7)
  · simpa only [adaptiveSpanLevel12839, adaptiveSpanNumerator12839, adaptiveSpanDenominator12839, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 6420) (by decide : 0 < 899)
        adaptiveSpanProfilesValid12839 adaptiveOrder12839 adaptiveSpanNumericCheck12839_8
        adaptiveSpanEven12839_8 adaptiveSpanWhole12839_8
        adaptiveSpanEvenEntries12839_8 adaptiveSpanWholeEntries12839_8
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanEvenDomain12839_8)
        (by rw [adaptiveSpanProfileLength12839]; exact adaptiveSpanWholeDomain12839_8)

/-- The complete finite histogram certificate for 11672 ≤ n ≤ 12839. -/
theorem adaptiveSpanHistogram12839 : DegreeIntervalCertificate 12839 adaptiveSpanPrimes12839
    (fun s v => sharpDegree (11672 / 2) 8 (adaptiveSpanNumerator12839 s)
      (adaptiveSpanDenominator12839 s) (totientDensity v))
    (fun s v => sharpDegree 11672 8 (adaptiveSpanNumerator12839 s)
      (adaptiveSpanDenominator12839 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows12839)
    adaptiveSpanPrimes12839
    (fun s => sharpDegree (11672 / 2) 8 (adaptiveSpanNumerator12839 s) (adaptiveSpanDenominator12839 s))
    (fun s => sharpDegree 11672 8 (adaptiveSpanNumerator12839 s) (adaptiveSpanDenominator12839 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid12839 adaptiveOrder12839 adaptivePermutationSemantics12839
    (by rw [adaptiveSpanProfileLength12839]; decide +kernel)
    adaptiveSpanLevel12839 adaptiveSpanTreeCache12839 adaptiveSpanTreeRepresents12839
    (fun j => adaptiveSpanWitness12839.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength12839
  · exact adaptiveSpanWitnessCheck12839

/-- Every required odd cycle for a dense set, throughout 11672 ≤ n ≤ 12839. -/
theorem adaptiveSpanInterval12839 {n : ℕ} (hLn : 11672 ≤ n) (hnU : n ≤ 12839)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes12839
    adaptiveSpanNumerator12839 adaptiveSpanDenominator12839 adaptiveSpanSharpTail12839
    adaptiveSpanPrimeSupport12839 adaptiveSpanHistogram12839 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail12839
#print axioms adaptiveSpanPrimeSupport12839
#print axioms adaptiveSpanHistogram12839
#print axioms adaptiveSpanInterval12839
end Erdos883Verified
