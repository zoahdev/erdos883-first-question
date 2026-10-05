import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate17091Metadata
import Erdos883AdaptiveSpan17091Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate17091PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes17091 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator17091 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator17091 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail17091 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes17091.length) :
    SharpTailCertificate 17091 (adaptiveSpanPrimes17091.take s)
      (adaptiveSpanNumerator17091 s) (adaptiveSpanDenominator17091 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 17091 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 17091 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 17091 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 17091 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 17091 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 17091 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 17091 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 17091 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 17091 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport17091 : ∀ u ∈ oddUniverse 17091,
    ∀ v ∈ oddUniverse 17091, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid17091 : AdaptiveProfileRowsValid adaptiveRows17091 :=
  coreProfileMetadataCheck_sound adaptiveMetadata17091

theorem adaptiveSpanProfileLength17091 : adaptiveRows17091.length = halfOdds 17091 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics17091
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache17091 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes17091.length) :
    (adaptiveSpanLevel17091 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel17091 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel17091, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache17091_0 adaptiveSpanWholeCache17091_0
  · simpa only [adaptiveSpanLevel17091, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache17091_1 adaptiveSpanWholeCache17091_1
  · simpa only [adaptiveSpanLevel17091, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache17091_2 adaptiveSpanWholeCache17091_2
  · simpa only [adaptiveSpanLevel17091, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache17091_3 adaptiveSpanWholeCache17091_3
  · simpa only [adaptiveSpanLevel17091, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache17091_4 adaptiveSpanWholeCache17091_4
  · simpa only [adaptiveSpanLevel17091, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache17091_5 adaptiveSpanWholeCache17091_5
  · simpa only [adaptiveSpanLevel17091, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache17091_6 adaptiveSpanWholeCache17091_6
  · simpa only [adaptiveSpanLevel17091, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache17091_7 adaptiveSpanWholeCache17091_7
  · simpa only [adaptiveSpanLevel17091, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache17091_8 adaptiveSpanWholeCache17091_8

theorem adaptiveSpanTreeRepresents17091 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes17091.length) :
    AdaptiveSpanTreeRepresents adaptiveRows17091 (halfOdds 17091)
      (sharpDegree (15538 / 2) 8 (adaptiveSpanNumerator17091 s) (adaptiveSpanDenominator17091 s))
      (sharpDegree 15538 8 (adaptiveSpanNumerator17091 s) (adaptiveSpanDenominator17091 s))
      (adaptiveSpanLevel17091 s).1 (adaptiveSpanLevel17091 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel17091, adaptiveSpanNumerator17091, adaptiveSpanDenominator17091, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 8546) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid17091 adaptiveOrder17091 adaptiveSpanNumericCheck17091_0
        adaptiveSpanEven17091_0 adaptiveSpanWhole17091_0
        adaptiveSpanEvenEntries17091_0 adaptiveSpanWholeEntries17091_0
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanEvenDomain17091_0)
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanWholeDomain17091_0)
  · simpa only [adaptiveSpanLevel17091, adaptiveSpanNumerator17091, adaptiveSpanDenominator17091, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 8546) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid17091 adaptiveOrder17091 adaptiveSpanNumericCheck17091_1
        adaptiveSpanEven17091_1 adaptiveSpanWhole17091_1
        adaptiveSpanEvenEntries17091_1 adaptiveSpanWholeEntries17091_1
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanEvenDomain17091_1)
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanWholeDomain17091_1)
  · simpa only [adaptiveSpanLevel17091, adaptiveSpanNumerator17091, adaptiveSpanDenominator17091, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 8546) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid17091 adaptiveOrder17091 adaptiveSpanNumericCheck17091_2
        adaptiveSpanEven17091_2 adaptiveSpanWhole17091_2
        adaptiveSpanEvenEntries17091_2 adaptiveSpanWholeEntries17091_2
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanEvenDomain17091_2)
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanWholeDomain17091_2)
  · simpa only [adaptiveSpanLevel17091, adaptiveSpanNumerator17091, adaptiveSpanDenominator17091, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 8546) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid17091 adaptiveOrder17091 adaptiveSpanNumericCheck17091_3
        adaptiveSpanEven17091_3 adaptiveSpanWhole17091_3
        adaptiveSpanEvenEntries17091_3 adaptiveSpanWholeEntries17091_3
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanEvenDomain17091_3)
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanWholeDomain17091_3)
  · simpa only [adaptiveSpanLevel17091, adaptiveSpanNumerator17091, adaptiveSpanDenominator17091, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 8546) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid17091 adaptiveOrder17091 adaptiveSpanNumericCheck17091_4
        adaptiveSpanEven17091_4 adaptiveSpanWhole17091_4
        adaptiveSpanEvenEntries17091_4 adaptiveSpanWholeEntries17091_4
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanEvenDomain17091_4)
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanWholeDomain17091_4)
  · simpa only [adaptiveSpanLevel17091, adaptiveSpanNumerator17091, adaptiveSpanDenominator17091, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 8546) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid17091 adaptiveOrder17091 adaptiveSpanNumericCheck17091_5
        adaptiveSpanEven17091_5 adaptiveSpanWhole17091_5
        adaptiveSpanEvenEntries17091_5 adaptiveSpanWholeEntries17091_5
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanEvenDomain17091_5)
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanWholeDomain17091_5)
  · simpa only [adaptiveSpanLevel17091, adaptiveSpanNumerator17091, adaptiveSpanDenominator17091, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 8546) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid17091 adaptiveOrder17091 adaptiveSpanNumericCheck17091_6
        adaptiveSpanEven17091_6 adaptiveSpanWhole17091_6
        adaptiveSpanEvenEntries17091_6 adaptiveSpanWholeEntries17091_6
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanEvenDomain17091_6)
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanWholeDomain17091_6)
  · simpa only [adaptiveSpanLevel17091, adaptiveSpanNumerator17091, adaptiveSpanDenominator17091, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 8546) (by decide : 0 < 667)
        adaptiveSpanProfilesValid17091 adaptiveOrder17091 adaptiveSpanNumericCheck17091_7
        adaptiveSpanEven17091_7 adaptiveSpanWhole17091_7
        adaptiveSpanEvenEntries17091_7 adaptiveSpanWholeEntries17091_7
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanEvenDomain17091_7)
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanWholeDomain17091_7)
  · simpa only [adaptiveSpanLevel17091, adaptiveSpanNumerator17091, adaptiveSpanDenominator17091, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 8546) (by decide : 0 < 899)
        adaptiveSpanProfilesValid17091 adaptiveOrder17091 adaptiveSpanNumericCheck17091_8
        adaptiveSpanEven17091_8 adaptiveSpanWhole17091_8
        adaptiveSpanEvenEntries17091_8 adaptiveSpanWholeEntries17091_8
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanEvenDomain17091_8)
        (by rw [adaptiveSpanProfileLength17091]; exact adaptiveSpanWholeDomain17091_8)

/-- The complete finite histogram certificate for 15538 ≤ n ≤ 17091. -/
theorem adaptiveSpanHistogram17091 : DegreeIntervalCertificate 17091 adaptiveSpanPrimes17091
    (fun s v => sharpDegree (15538 / 2) 8 (adaptiveSpanNumerator17091 s)
      (adaptiveSpanDenominator17091 s) (totientDensity v))
    (fun s v => sharpDegree 15538 8 (adaptiveSpanNumerator17091 s)
      (adaptiveSpanDenominator17091 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows17091)
    adaptiveSpanPrimes17091
    (fun s => sharpDegree (15538 / 2) 8 (adaptiveSpanNumerator17091 s) (adaptiveSpanDenominator17091 s))
    (fun s => sharpDegree 15538 8 (adaptiveSpanNumerator17091 s) (adaptiveSpanDenominator17091 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid17091 adaptiveOrder17091 adaptivePermutationSemantics17091
    (by rw [adaptiveSpanProfileLength17091]; decide +kernel)
    adaptiveSpanLevel17091 adaptiveSpanTreeCache17091 adaptiveSpanTreeRepresents17091
    (fun j => adaptiveSpanWitness17091.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength17091
  · exact adaptiveSpanWitnessCheck17091

/-- Every required odd cycle for a dense set, throughout 15538 ≤ n ≤ 17091. -/
theorem adaptiveSpanInterval17091 {n : ℕ} (hLn : 15538 ≤ n) (hnU : n ≤ 17091)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes17091
    adaptiveSpanNumerator17091 adaptiveSpanDenominator17091 adaptiveSpanSharpTail17091
    adaptiveSpanPrimeSupport17091 adaptiveSpanHistogram17091 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail17091
#print axioms adaptiveSpanPrimeSupport17091
#print axioms adaptiveSpanHistogram17091
#print axioms adaptiveSpanInterval17091
end Erdos883Verified
