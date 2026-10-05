import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate53655Metadata
import Erdos883AdaptiveSpan53655Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate53655PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes53655 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator53655 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 34560
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator53655 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 46189
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail53655 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes53655.length) :
    SharpTailCertificate 53655 (adaptiveSpanPrimes53655.take s)
      (adaptiveSpanNumerator53655 s) (adaptiveSpanDenominator53655 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 53655 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 53655 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 53655 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 53655 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 53655 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 53655 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 53655 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 53655 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 53655 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport53655 : ∀ u ∈ oddUniverse 53655,
    ∀ v ∈ oddUniverse 53655, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid53655 : AdaptiveProfileRowsValid adaptiveRows53655 :=
  coreProfileMetadataCheck_sound adaptiveMetadata53655

theorem adaptiveSpanProfileLength53655 : adaptiveRows53655.length = halfOdds 53655 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics53655
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache53655 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes53655.length) :
    (adaptiveSpanLevel53655 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel53655 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel53655, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache53655_0 adaptiveSpanWholeCache53655_0
  · simpa only [adaptiveSpanLevel53655, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache53655_1 adaptiveSpanWholeCache53655_1
  · simpa only [adaptiveSpanLevel53655, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache53655_2 adaptiveSpanWholeCache53655_2
  · simpa only [adaptiveSpanLevel53655, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache53655_3 adaptiveSpanWholeCache53655_3
  · simpa only [adaptiveSpanLevel53655, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache53655_4 adaptiveSpanWholeCache53655_4
  · simpa only [adaptiveSpanLevel53655, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache53655_5 adaptiveSpanWholeCache53655_5
  · simpa only [adaptiveSpanLevel53655, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache53655_6 adaptiveSpanWholeCache53655_6
  · simpa only [adaptiveSpanLevel53655, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache53655_7 adaptiveSpanWholeCache53655_7
  · simpa only [adaptiveSpanLevel53655, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache53655_8 adaptiveSpanWholeCache53655_8

theorem adaptiveSpanTreeRepresents53655 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes53655.length) :
    AdaptiveSpanTreeRepresents adaptiveRows53655 (halfOdds 53655)
      (sharpDegree (48778 / 2) 8 (adaptiveSpanNumerator53655 s) (adaptiveSpanDenominator53655 s))
      (sharpDegree 48778 8 (adaptiveSpanNumerator53655 s) (adaptiveSpanDenominator53655 s))
      (adaptiveSpanLevel53655 s).1 (adaptiveSpanLevel53655 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel53655, adaptiveSpanNumerator53655, adaptiveSpanDenominator53655, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 26828) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid53655 adaptiveOrder53655 adaptiveSpanNumericCheck53655_0
        adaptiveSpanEven53655_0 adaptiveSpanWhole53655_0
        adaptiveSpanEvenEntries53655_0 adaptiveSpanWholeEntries53655_0
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanEvenDomain53655_0)
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanWholeDomain53655_0)
  · simpa only [adaptiveSpanLevel53655, adaptiveSpanNumerator53655, adaptiveSpanDenominator53655, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 26828) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid53655 adaptiveOrder53655 adaptiveSpanNumericCheck53655_1
        adaptiveSpanEven53655_1 adaptiveSpanWhole53655_1
        adaptiveSpanEvenEntries53655_1 adaptiveSpanWholeEntries53655_1
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanEvenDomain53655_1)
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanWholeDomain53655_1)
  · simpa only [adaptiveSpanLevel53655, adaptiveSpanNumerator53655, adaptiveSpanDenominator53655, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 26828) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid53655 adaptiveOrder53655 adaptiveSpanNumericCheck53655_2
        adaptiveSpanEven53655_2 adaptiveSpanWhole53655_2
        adaptiveSpanEvenEntries53655_2 adaptiveSpanWholeEntries53655_2
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanEvenDomain53655_2)
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanWholeDomain53655_2)
  · simpa only [adaptiveSpanLevel53655, adaptiveSpanNumerator53655, adaptiveSpanDenominator53655, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 26828) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid53655 adaptiveOrder53655 adaptiveSpanNumericCheck53655_3
        adaptiveSpanEven53655_3 adaptiveSpanWhole53655_3
        adaptiveSpanEvenEntries53655_3 adaptiveSpanWholeEntries53655_3
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanEvenDomain53655_3)
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanWholeDomain53655_3)
  · simpa only [adaptiveSpanLevel53655, adaptiveSpanNumerator53655, adaptiveSpanDenominator53655, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 26828) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid53655 adaptiveOrder53655 adaptiveSpanNumericCheck53655_4
        adaptiveSpanEven53655_4 adaptiveSpanWhole53655_4
        adaptiveSpanEvenEntries53655_4 adaptiveSpanWholeEntries53655_4
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanEvenDomain53655_4)
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanWholeDomain53655_4)
  · simpa only [adaptiveSpanLevel53655, adaptiveSpanNumerator53655, adaptiveSpanDenominator53655, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 26828) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid53655 adaptiveOrder53655 adaptiveSpanNumericCheck53655_5
        adaptiveSpanEven53655_5 adaptiveSpanWhole53655_5
        adaptiveSpanEvenEntries53655_5 adaptiveSpanWholeEntries53655_5
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanEvenDomain53655_5)
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanWholeDomain53655_5)
  · simpa only [adaptiveSpanLevel53655, adaptiveSpanNumerator53655, adaptiveSpanDenominator53655, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 26828) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid53655 adaptiveOrder53655 adaptiveSpanNumericCheck53655_6
        adaptiveSpanEven53655_6 adaptiveSpanWhole53655_6
        adaptiveSpanEvenEntries53655_6 adaptiveSpanWholeEntries53655_6
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanEvenDomain53655_6)
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanWholeDomain53655_6)
  · simpa only [adaptiveSpanLevel53655, adaptiveSpanNumerator53655, adaptiveSpanDenominator53655, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 26828) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid53655 adaptiveOrder53655 adaptiveSpanNumericCheck53655_7
        adaptiveSpanEven53655_7 adaptiveSpanWhole53655_7
        adaptiveSpanEvenEntries53655_7 adaptiveSpanWholeEntries53655_7
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanEvenDomain53655_7)
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanWholeDomain53655_7)
  · simpa only [adaptiveSpanLevel53655, adaptiveSpanNumerator53655, adaptiveSpanDenominator53655, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 26828) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid53655 adaptiveOrder53655 adaptiveSpanNumericCheck53655_8
        adaptiveSpanEven53655_8 adaptiveSpanWhole53655_8
        adaptiveSpanEvenEntries53655_8 adaptiveSpanWholeEntries53655_8
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanEvenDomain53655_8)
        (by rw [adaptiveSpanProfileLength53655]; exact adaptiveSpanWholeDomain53655_8)

/-- The complete finite histogram certificate for 48778 ≤ n ≤ 53655. -/
theorem adaptiveSpanHistogram53655 : DegreeIntervalCertificate 53655 adaptiveSpanPrimes53655
    (fun s v => sharpDegree (48778 / 2) 8 (adaptiveSpanNumerator53655 s)
      (adaptiveSpanDenominator53655 s) (totientDensity v))
    (fun s v => sharpDegree 48778 8 (adaptiveSpanNumerator53655 s)
      (adaptiveSpanDenominator53655 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows53655)
    adaptiveSpanPrimes53655
    (fun s => sharpDegree (48778 / 2) 8 (adaptiveSpanNumerator53655 s) (adaptiveSpanDenominator53655 s))
    (fun s => sharpDegree 48778 8 (adaptiveSpanNumerator53655 s) (adaptiveSpanDenominator53655 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid53655 adaptiveOrder53655 adaptivePermutationSemantics53655
    (by rw [adaptiveSpanProfileLength53655]; decide +kernel)
    adaptiveSpanLevel53655 adaptiveSpanTreeCache53655 adaptiveSpanTreeRepresents53655
    (fun j => adaptiveSpanWitness53655.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength53655
  · exact adaptiveSpanWitnessCheck53655

/-- Every required odd cycle for a dense set, throughout 48778 ≤ n ≤ 53655. -/
theorem adaptiveSpanInterval53655 {n : ℕ} (hLn : 48778 ≤ n) (hnU : n ≤ 53655)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes53655
    adaptiveSpanNumerator53655 adaptiveSpanDenominator53655 adaptiveSpanSharpTail53655
    adaptiveSpanPrimeSupport53655 adaptiveSpanHistogram53655 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail53655
#print axioms adaptiveSpanPrimeSupport53655
#print axioms adaptiveSpanHistogram53655
#print axioms adaptiveSpanInterval53655
end Erdos883Verified
