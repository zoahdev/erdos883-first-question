import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate20682Metadata
import Erdos883AdaptiveSpan20682Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate20682PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes20682 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator20682 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 840

def adaptiveSpanDenominator20682 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 899

theorem adaptiveSpanSharpTail20682 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes20682.length) :
    SharpTailCertificate 20682 (adaptiveSpanPrimes20682.take s)
      (adaptiveSpanNumerator20682 s) (adaptiveSpanDenominator20682 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 20682 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 20682 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 20682 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 20682 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 20682 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 20682 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 20682 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 20682 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 20682 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport20682 : ∀ u ∈ oddUniverse 20682,
    ∀ v ∈ oddUniverse 20682, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid20682 : AdaptiveProfileRowsValid adaptiveRows20682 :=
  coreProfileMetadataCheck_sound adaptiveMetadata20682

theorem adaptiveSpanProfileLength20682 : adaptiveRows20682.length = halfOdds 20682 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics20682
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache20682 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes20682.length) :
    (adaptiveSpanLevel20682 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel20682 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel20682, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache20682_0 adaptiveSpanWholeCache20682_0
  · simpa only [adaptiveSpanLevel20682, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache20682_1 adaptiveSpanWholeCache20682_1
  · simpa only [adaptiveSpanLevel20682, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache20682_2 adaptiveSpanWholeCache20682_2
  · simpa only [adaptiveSpanLevel20682, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache20682_3 adaptiveSpanWholeCache20682_3
  · simpa only [adaptiveSpanLevel20682, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache20682_4 adaptiveSpanWholeCache20682_4
  · simpa only [adaptiveSpanLevel20682, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache20682_5 adaptiveSpanWholeCache20682_5
  · simpa only [adaptiveSpanLevel20682, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache20682_6 adaptiveSpanWholeCache20682_6
  · simpa only [adaptiveSpanLevel20682, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache20682_7 adaptiveSpanWholeCache20682_7
  · simpa only [adaptiveSpanLevel20682, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache20682_8 adaptiveSpanWholeCache20682_8

theorem adaptiveSpanTreeRepresents20682 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes20682.length) :
    AdaptiveSpanTreeRepresents adaptiveRows20682 (halfOdds 20682)
      (sharpDegree (18802 / 2) 8 (adaptiveSpanNumerator20682 s) (adaptiveSpanDenominator20682 s))
      (sharpDegree 18802 8 (adaptiveSpanNumerator20682 s) (adaptiveSpanDenominator20682 s))
      (adaptiveSpanLevel20682 s).1 (adaptiveSpanLevel20682 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel20682, adaptiveSpanNumerator20682, adaptiveSpanDenominator20682, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 10341) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid20682 adaptiveOrder20682 adaptiveSpanNumericCheck20682_0
        adaptiveSpanEven20682_0 adaptiveSpanWhole20682_0
        adaptiveSpanEvenEntries20682_0 adaptiveSpanWholeEntries20682_0
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanEvenDomain20682_0)
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanWholeDomain20682_0)
  · simpa only [adaptiveSpanLevel20682, adaptiveSpanNumerator20682, adaptiveSpanDenominator20682, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 10341) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid20682 adaptiveOrder20682 adaptiveSpanNumericCheck20682_1
        adaptiveSpanEven20682_1 adaptiveSpanWhole20682_1
        adaptiveSpanEvenEntries20682_1 adaptiveSpanWholeEntries20682_1
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanEvenDomain20682_1)
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanWholeDomain20682_1)
  · simpa only [adaptiveSpanLevel20682, adaptiveSpanNumerator20682, adaptiveSpanDenominator20682, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 10341) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid20682 adaptiveOrder20682 adaptiveSpanNumericCheck20682_2
        adaptiveSpanEven20682_2 adaptiveSpanWhole20682_2
        adaptiveSpanEvenEntries20682_2 adaptiveSpanWholeEntries20682_2
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanEvenDomain20682_2)
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanWholeDomain20682_2)
  · simpa only [adaptiveSpanLevel20682, adaptiveSpanNumerator20682, adaptiveSpanDenominator20682, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 10341) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid20682 adaptiveOrder20682 adaptiveSpanNumericCheck20682_3
        adaptiveSpanEven20682_3 adaptiveSpanWhole20682_3
        adaptiveSpanEvenEntries20682_3 adaptiveSpanWholeEntries20682_3
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanEvenDomain20682_3)
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanWholeDomain20682_3)
  · simpa only [adaptiveSpanLevel20682, adaptiveSpanNumerator20682, adaptiveSpanDenominator20682, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 10341) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid20682 adaptiveOrder20682 adaptiveSpanNumericCheck20682_4
        adaptiveSpanEven20682_4 adaptiveSpanWhole20682_4
        adaptiveSpanEvenEntries20682_4 adaptiveSpanWholeEntries20682_4
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanEvenDomain20682_4)
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanWholeDomain20682_4)
  · simpa only [adaptiveSpanLevel20682, adaptiveSpanNumerator20682, adaptiveSpanDenominator20682, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 10341) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid20682 adaptiveOrder20682 adaptiveSpanNumericCheck20682_5
        adaptiveSpanEven20682_5 adaptiveSpanWhole20682_5
        adaptiveSpanEvenEntries20682_5 adaptiveSpanWholeEntries20682_5
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanEvenDomain20682_5)
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanWholeDomain20682_5)
  · simpa only [adaptiveSpanLevel20682, adaptiveSpanNumerator20682, adaptiveSpanDenominator20682, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 10341) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid20682 adaptiveOrder20682 adaptiveSpanNumericCheck20682_6
        adaptiveSpanEven20682_6 adaptiveSpanWhole20682_6
        adaptiveSpanEvenEntries20682_6 adaptiveSpanWholeEntries20682_6
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanEvenDomain20682_6)
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanWholeDomain20682_6)
  · simpa only [adaptiveSpanLevel20682, adaptiveSpanNumerator20682, adaptiveSpanDenominator20682, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 10341) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid20682 adaptiveOrder20682 adaptiveSpanNumericCheck20682_7
        adaptiveSpanEven20682_7 adaptiveSpanWhole20682_7
        adaptiveSpanEvenEntries20682_7 adaptiveSpanWholeEntries20682_7
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanEvenDomain20682_7)
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanWholeDomain20682_7)
  · simpa only [adaptiveSpanLevel20682, adaptiveSpanNumerator20682, adaptiveSpanDenominator20682, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 10341) (by decide : 0 < 899)
        adaptiveSpanProfilesValid20682 adaptiveOrder20682 adaptiveSpanNumericCheck20682_8
        adaptiveSpanEven20682_8 adaptiveSpanWhole20682_8
        adaptiveSpanEvenEntries20682_8 adaptiveSpanWholeEntries20682_8
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanEvenDomain20682_8)
        (by rw [adaptiveSpanProfileLength20682]; exact adaptiveSpanWholeDomain20682_8)

/-- The complete finite histogram certificate for 18802 ≤ n ≤ 20682. -/
theorem adaptiveSpanHistogram20682 : DegreeIntervalCertificate 20682 adaptiveSpanPrimes20682
    (fun s v => sharpDegree (18802 / 2) 8 (adaptiveSpanNumerator20682 s)
      (adaptiveSpanDenominator20682 s) (totientDensity v))
    (fun s v => sharpDegree 18802 8 (adaptiveSpanNumerator20682 s)
      (adaptiveSpanDenominator20682 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows20682)
    adaptiveSpanPrimes20682
    (fun s => sharpDegree (18802 / 2) 8 (adaptiveSpanNumerator20682 s) (adaptiveSpanDenominator20682 s))
    (fun s => sharpDegree 18802 8 (adaptiveSpanNumerator20682 s) (adaptiveSpanDenominator20682 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid20682 adaptiveOrder20682 adaptivePermutationSemantics20682
    (by rw [adaptiveSpanProfileLength20682]; decide +kernel)
    adaptiveSpanLevel20682 adaptiveSpanTreeCache20682 adaptiveSpanTreeRepresents20682
    (fun j => adaptiveSpanWitness20682.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength20682
  · exact adaptiveSpanWitnessCheck20682

/-- Every required odd cycle for a dense set, throughout 18802 ≤ n ≤ 20682. -/
theorem adaptiveSpanInterval20682 {n : ℕ} (hLn : 18802 ≤ n) (hnU : n ≤ 20682)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes20682
    adaptiveSpanNumerator20682 adaptiveSpanDenominator20682 adaptiveSpanSharpTail20682
    adaptiveSpanPrimeSupport20682 adaptiveSpanHistogram20682 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail20682
#print axioms adaptiveSpanPrimeSupport20682
#print axioms adaptiveSpanHistogram20682
#print axioms adaptiveSpanInterval20682
end Erdos883Verified
