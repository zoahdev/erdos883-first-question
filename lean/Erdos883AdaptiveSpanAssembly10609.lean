import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate10609Metadata
import Erdos883AdaptiveSpan10609Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate10609PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes10609 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator10609 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 396
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator10609 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 437
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail10609 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes10609.length) :
    SharpTailCertificate 10609 (adaptiveSpanPrimes10609.take s)
      (adaptiveSpanNumerator10609 s) (adaptiveSpanDenominator10609 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 10609 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 10609 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 10609 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 10609 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 10609 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 10609 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 10609 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 10609 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 10609 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport10609 : ∀ u ∈ oddUniverse 10609,
    ∀ v ∈ oddUniverse 10609, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid10609 : AdaptiveProfileRowsValid adaptiveRows10609 :=
  coreProfileMetadataCheck_sound adaptiveMetadata10609

theorem adaptiveSpanProfileLength10609 : adaptiveRows10609.length = halfOdds 10609 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics10609
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache10609 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes10609.length) :
    (adaptiveSpanLevel10609 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel10609 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel10609, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache10609_0 adaptiveSpanWholeCache10609_0
  · simpa only [adaptiveSpanLevel10609, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache10609_1 adaptiveSpanWholeCache10609_1
  · simpa only [adaptiveSpanLevel10609, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache10609_2 adaptiveSpanWholeCache10609_2
  · simpa only [adaptiveSpanLevel10609, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache10609_3 adaptiveSpanWholeCache10609_3
  · simpa only [adaptiveSpanLevel10609, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache10609_4 adaptiveSpanWholeCache10609_4
  · simpa only [adaptiveSpanLevel10609, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache10609_5 adaptiveSpanWholeCache10609_5
  · simpa only [adaptiveSpanLevel10609, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache10609_6 adaptiveSpanWholeCache10609_6
  · simpa only [adaptiveSpanLevel10609, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache10609_7 adaptiveSpanWholeCache10609_7
  · simpa only [adaptiveSpanLevel10609, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache10609_8 adaptiveSpanWholeCache10609_8

theorem adaptiveSpanTreeRepresents10609 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes10609.length) :
    AdaptiveSpanTreeRepresents adaptiveRows10609 (halfOdds 10609)
      (sharpDegree (9645 / 2) 8 (adaptiveSpanNumerator10609 s) (adaptiveSpanDenominator10609 s))
      (sharpDegree 9645 8 (adaptiveSpanNumerator10609 s) (adaptiveSpanDenominator10609 s))
      (adaptiveSpanLevel10609 s).1 (adaptiveSpanLevel10609 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel10609, adaptiveSpanNumerator10609, adaptiveSpanDenominator10609, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5305) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid10609 adaptiveOrder10609 adaptiveSpanNumericCheck10609_0
        adaptiveSpanEven10609_0 adaptiveSpanWhole10609_0
        adaptiveSpanEvenEntries10609_0 adaptiveSpanWholeEntries10609_0
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanEvenDomain10609_0)
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanWholeDomain10609_0)
  · simpa only [adaptiveSpanLevel10609, adaptiveSpanNumerator10609, adaptiveSpanDenominator10609, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5305) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid10609 adaptiveOrder10609 adaptiveSpanNumericCheck10609_1
        adaptiveSpanEven10609_1 adaptiveSpanWhole10609_1
        adaptiveSpanEvenEntries10609_1 adaptiveSpanWholeEntries10609_1
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanEvenDomain10609_1)
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanWholeDomain10609_1)
  · simpa only [adaptiveSpanLevel10609, adaptiveSpanNumerator10609, adaptiveSpanDenominator10609, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5305) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid10609 adaptiveOrder10609 adaptiveSpanNumericCheck10609_2
        adaptiveSpanEven10609_2 adaptiveSpanWhole10609_2
        adaptiveSpanEvenEntries10609_2 adaptiveSpanWholeEntries10609_2
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanEvenDomain10609_2)
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanWholeDomain10609_2)
  · simpa only [adaptiveSpanLevel10609, adaptiveSpanNumerator10609, adaptiveSpanDenominator10609, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5305) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid10609 adaptiveOrder10609 adaptiveSpanNumericCheck10609_3
        adaptiveSpanEven10609_3 adaptiveSpanWhole10609_3
        adaptiveSpanEvenEntries10609_3 adaptiveSpanWholeEntries10609_3
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanEvenDomain10609_3)
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanWholeDomain10609_3)
  · simpa only [adaptiveSpanLevel10609, adaptiveSpanNumerator10609, adaptiveSpanDenominator10609, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5305) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid10609 adaptiveOrder10609 adaptiveSpanNumericCheck10609_4
        adaptiveSpanEven10609_4 adaptiveSpanWhole10609_4
        adaptiveSpanEvenEntries10609_4 adaptiveSpanWholeEntries10609_4
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanEvenDomain10609_4)
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanWholeDomain10609_4)
  · simpa only [adaptiveSpanLevel10609, adaptiveSpanNumerator10609, adaptiveSpanDenominator10609, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5305) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid10609 adaptiveOrder10609 adaptiveSpanNumericCheck10609_5
        adaptiveSpanEven10609_5 adaptiveSpanWhole10609_5
        adaptiveSpanEvenEntries10609_5 adaptiveSpanWholeEntries10609_5
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanEvenDomain10609_5)
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanWholeDomain10609_5)
  · simpa only [adaptiveSpanLevel10609, adaptiveSpanNumerator10609, adaptiveSpanDenominator10609, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5305) (by decide : 0 < 437)
        adaptiveSpanProfilesValid10609 adaptiveOrder10609 adaptiveSpanNumericCheck10609_6
        adaptiveSpanEven10609_6 adaptiveSpanWhole10609_6
        adaptiveSpanEvenEntries10609_6 adaptiveSpanWholeEntries10609_6
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanEvenDomain10609_6)
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanWholeDomain10609_6)
  · simpa only [adaptiveSpanLevel10609, adaptiveSpanNumerator10609, adaptiveSpanDenominator10609, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5305) (by decide : 0 < 667)
        adaptiveSpanProfilesValid10609 adaptiveOrder10609 adaptiveSpanNumericCheck10609_7
        adaptiveSpanEven10609_7 adaptiveSpanWhole10609_7
        adaptiveSpanEvenEntries10609_7 adaptiveSpanWholeEntries10609_7
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanEvenDomain10609_7)
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanWholeDomain10609_7)
  · simpa only [adaptiveSpanLevel10609, adaptiveSpanNumerator10609, adaptiveSpanDenominator10609, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5305) (by decide : 0 < 899)
        adaptiveSpanProfilesValid10609 adaptiveOrder10609 adaptiveSpanNumericCheck10609_8
        adaptiveSpanEven10609_8 adaptiveSpanWhole10609_8
        adaptiveSpanEvenEntries10609_8 adaptiveSpanWholeEntries10609_8
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanEvenDomain10609_8)
        (by rw [adaptiveSpanProfileLength10609]; exact adaptiveSpanWholeDomain10609_8)

/-- The complete finite histogram certificate for 9645 ≤ n ≤ 10609. -/
theorem adaptiveSpanHistogram10609 : DegreeIntervalCertificate 10609 adaptiveSpanPrimes10609
    (fun s v => sharpDegree (9645 / 2) 8 (adaptiveSpanNumerator10609 s)
      (adaptiveSpanDenominator10609 s) (totientDensity v))
    (fun s v => sharpDegree 9645 8 (adaptiveSpanNumerator10609 s)
      (adaptiveSpanDenominator10609 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows10609)
    adaptiveSpanPrimes10609
    (fun s => sharpDegree (9645 / 2) 8 (adaptiveSpanNumerator10609 s) (adaptiveSpanDenominator10609 s))
    (fun s => sharpDegree 9645 8 (adaptiveSpanNumerator10609 s) (adaptiveSpanDenominator10609 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid10609 adaptiveOrder10609 adaptivePermutationSemantics10609
    (by rw [adaptiveSpanProfileLength10609]; decide +kernel)
    adaptiveSpanLevel10609 adaptiveSpanTreeCache10609 adaptiveSpanTreeRepresents10609
    (fun j => adaptiveSpanWitness10609.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength10609
  · exact adaptiveSpanWitnessCheck10609

/-- Every required odd cycle for a dense set, throughout 9645 ≤ n ≤ 10609. -/
theorem adaptiveSpanInterval10609 {n : ℕ} (hLn : 9645 ≤ n) (hnU : n ≤ 10609)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes10609
    adaptiveSpanNumerator10609 adaptiveSpanDenominator10609 adaptiveSpanSharpTail10609
    adaptiveSpanPrimeSupport10609 adaptiveSpanHistogram10609 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail10609
#print axioms adaptiveSpanPrimeSupport10609
#print axioms adaptiveSpanHistogram10609
#print axioms adaptiveSpanInterval10609
end Erdos883Verified
