import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate185246Metadata
import Erdos883AdaptiveSpan185246Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate185246PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes185246 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator185246 : ℕ → ℕ
  | 0 => 5760
  | 1 => 46080
  | 2 => 11520
  | 3 => 34560
  | 4 => 76032
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator185246 : ℕ → ℕ
  | 0 => 15015
  | 1 => 85085
  | 2 => 17017
  | 3 => 46189
  | 4 => 96577
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail185246 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes185246.length) :
    SharpTailCertificate 185246 (adaptiveSpanPrimes185246.take s)
      (adaptiveSpanNumerator185246 s) (adaptiveSpanDenominator185246 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 185246 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 185246 [3] 46080 85085
    refine ⟨by decide, {5, 7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 185246 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 185246 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 185246 [3, 5, 7, 11] 76032 96577
    refine ⟨by decide, {13, 17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 185246 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 185246 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 185246 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 185246 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport185246 : ∀ u ∈ oddUniverse 185246,
    ∀ v ∈ oddUniverse 185246, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid185246 : AdaptiveProfileRowsValid adaptiveRows185246 :=
  coreProfileMetadataCheck_sound adaptiveMetadata185246

theorem adaptiveSpanProfileLength185246 : adaptiveRows185246.length = halfOdds 185246 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics185246
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache185246 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes185246.length) :
    (adaptiveSpanLevel185246 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel185246 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel185246, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache185246_0 adaptiveSpanWholeCache185246_0
  · simpa only [adaptiveSpanLevel185246, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache185246_1 adaptiveSpanWholeCache185246_1
  · simpa only [adaptiveSpanLevel185246, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache185246_2 adaptiveSpanWholeCache185246_2
  · simpa only [adaptiveSpanLevel185246, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache185246_3 adaptiveSpanWholeCache185246_3
  · simpa only [adaptiveSpanLevel185246, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache185246_4 adaptiveSpanWholeCache185246_4
  · simpa only [adaptiveSpanLevel185246, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache185246_5 adaptiveSpanWholeCache185246_5
  · simpa only [adaptiveSpanLevel185246, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache185246_6 adaptiveSpanWholeCache185246_6
  · simpa only [adaptiveSpanLevel185246, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache185246_7 adaptiveSpanWholeCache185246_7
  · simpa only [adaptiveSpanLevel185246, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache185246_8 adaptiveSpanWholeCache185246_8

theorem adaptiveSpanTreeRepresents185246 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes185246.length) :
    AdaptiveSpanTreeRepresents adaptiveRows185246 (halfOdds 185246)
      (sharpDegree (168406 / 2) 9 (adaptiveSpanNumerator185246 s) (adaptiveSpanDenominator185246 s))
      (sharpDegree 168406 9 (adaptiveSpanNumerator185246 s) (adaptiveSpanDenominator185246 s))
      (adaptiveSpanLevel185246 s).1 (adaptiveSpanLevel185246 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel185246, adaptiveSpanNumerator185246, adaptiveSpanDenominator185246, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 92623) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid185246 adaptiveOrder185246 adaptiveSpanNumericCheck185246_0
        adaptiveSpanEven185246_0 adaptiveSpanWhole185246_0
        adaptiveSpanEvenEntries185246_0 adaptiveSpanWholeEntries185246_0
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanEvenDomain185246_0)
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanWholeDomain185246_0)
  · simpa only [adaptiveSpanLevel185246, adaptiveSpanNumerator185246, adaptiveSpanDenominator185246, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 92623) (by decide : 0 < 85085)
        adaptiveSpanProfilesValid185246 adaptiveOrder185246 adaptiveSpanNumericCheck185246_1
        adaptiveSpanEven185246_1 adaptiveSpanWhole185246_1
        adaptiveSpanEvenEntries185246_1 adaptiveSpanWholeEntries185246_1
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanEvenDomain185246_1)
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanWholeDomain185246_1)
  · simpa only [adaptiveSpanLevel185246, adaptiveSpanNumerator185246, adaptiveSpanDenominator185246, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 92623) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid185246 adaptiveOrder185246 adaptiveSpanNumericCheck185246_2
        adaptiveSpanEven185246_2 adaptiveSpanWhole185246_2
        adaptiveSpanEvenEntries185246_2 adaptiveSpanWholeEntries185246_2
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanEvenDomain185246_2)
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanWholeDomain185246_2)
  · simpa only [adaptiveSpanLevel185246, adaptiveSpanNumerator185246, adaptiveSpanDenominator185246, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 92623) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid185246 adaptiveOrder185246 adaptiveSpanNumericCheck185246_3
        adaptiveSpanEven185246_3 adaptiveSpanWhole185246_3
        adaptiveSpanEvenEntries185246_3 adaptiveSpanWholeEntries185246_3
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanEvenDomain185246_3)
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanWholeDomain185246_3)
  · simpa only [adaptiveSpanLevel185246, adaptiveSpanNumerator185246, adaptiveSpanDenominator185246, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 92623) (by decide : 0 < 96577)
        adaptiveSpanProfilesValid185246 adaptiveOrder185246 adaptiveSpanNumericCheck185246_4
        adaptiveSpanEven185246_4 adaptiveSpanWhole185246_4
        adaptiveSpanEvenEntries185246_4 adaptiveSpanWholeEntries185246_4
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanEvenDomain185246_4)
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanWholeDomain185246_4)
  · simpa only [adaptiveSpanLevel185246, adaptiveSpanNumerator185246, adaptiveSpanDenominator185246, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 92623) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid185246 adaptiveOrder185246 adaptiveSpanNumericCheck185246_5
        adaptiveSpanEven185246_5 adaptiveSpanWhole185246_5
        adaptiveSpanEvenEntries185246_5 adaptiveSpanWholeEntries185246_5
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanEvenDomain185246_5)
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanWholeDomain185246_5)
  · simpa only [adaptiveSpanLevel185246, adaptiveSpanNumerator185246, adaptiveSpanDenominator185246, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 92623) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid185246 adaptiveOrder185246 adaptiveSpanNumericCheck185246_6
        adaptiveSpanEven185246_6 adaptiveSpanWhole185246_6
        adaptiveSpanEvenEntries185246_6 adaptiveSpanWholeEntries185246_6
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanEvenDomain185246_6)
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanWholeDomain185246_6)
  · simpa only [adaptiveSpanLevel185246, adaptiveSpanNumerator185246, adaptiveSpanDenominator185246, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 92623) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid185246 adaptiveOrder185246 adaptiveSpanNumericCheck185246_7
        adaptiveSpanEven185246_7 adaptiveSpanWhole185246_7
        adaptiveSpanEvenEntries185246_7 adaptiveSpanWholeEntries185246_7
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanEvenDomain185246_7)
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanWholeDomain185246_7)
  · simpa only [adaptiveSpanLevel185246, adaptiveSpanNumerator185246, adaptiveSpanDenominator185246, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 92623) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid185246 adaptiveOrder185246 adaptiveSpanNumericCheck185246_8
        adaptiveSpanEven185246_8 adaptiveSpanWhole185246_8
        adaptiveSpanEvenEntries185246_8 adaptiveSpanWholeEntries185246_8
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanEvenDomain185246_8)
        (by rw [adaptiveSpanProfileLength185246]; exact adaptiveSpanWholeDomain185246_8)

/-- The complete finite histogram certificate for 168406 ≤ n ≤ 185246. -/
theorem adaptiveSpanHistogram185246 : DegreeIntervalCertificate 185246 adaptiveSpanPrimes185246
    (fun s v => sharpDegree (168406 / 2) 9 (adaptiveSpanNumerator185246 s)
      (adaptiveSpanDenominator185246 s) (totientDensity v))
    (fun s v => sharpDegree 168406 9 (adaptiveSpanNumerator185246 s)
      (adaptiveSpanDenominator185246 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows185246)
    adaptiveSpanPrimes185246
    (fun s => sharpDegree (168406 / 2) 9 (adaptiveSpanNumerator185246 s) (adaptiveSpanDenominator185246 s))
    (fun s => sharpDegree 168406 9 (adaptiveSpanNumerator185246 s) (adaptiveSpanDenominator185246 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid185246 adaptiveOrder185246 adaptivePermutationSemantics185246
    (by rw [adaptiveSpanProfileLength185246]; decide +kernel)
    adaptiveSpanLevel185246 adaptiveSpanTreeCache185246 adaptiveSpanTreeRepresents185246
    (fun j => adaptiveSpanWitness185246.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength185246
  · exact adaptiveSpanWitnessCheck185246

/-- Every required odd cycle for a dense set, throughout 168406 ≤ n ≤ 185246. -/
theorem adaptiveSpanInterval185246 {n : ℕ} (hLn : 168406 ≤ n) (hnU : n ≤ 185246)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes185246
    adaptiveSpanNumerator185246 adaptiveSpanDenominator185246 adaptiveSpanSharpTail185246
    adaptiveSpanPrimeSupport185246 adaptiveSpanHistogram185246 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail185246
#print axioms adaptiveSpanPrimeSupport185246
#print axioms adaptiveSpanHistogram185246
#print axioms adaptiveSpanInterval185246
end Erdos883Verified
