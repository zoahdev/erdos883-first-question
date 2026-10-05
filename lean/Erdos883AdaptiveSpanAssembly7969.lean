import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate7969Metadata
import Erdos883AdaptiveSpan7969Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes7969 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator7969 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 396
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator7969 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 437
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail7969 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes7969.length) :
    SharpTailCertificate 7969 (adaptiveSpanPrimes7969.take s)
      (adaptiveSpanNumerator7969 s) (adaptiveSpanDenominator7969 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 7969 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7969 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7969 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7969 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7969 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7969 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7969 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7969 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7969 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport7969 : ∀ u ∈ oddUniverse 7969,
    ∀ v ∈ oddUniverse 7969, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid7969 : AdaptiveProfileRowsValid adaptiveRows7969 :=
  coreProfileMetadataCheck_sound adaptiveMetadata7969

theorem adaptiveSpanProfileLength7969 : adaptiveRows7969.length = halfOdds 7969 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation7969)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache7969 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes7969.length) :
    (adaptiveSpanLevel7969 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel7969 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel7969, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7969_0 adaptiveSpanWholeCache7969_0
  · simpa only [adaptiveSpanLevel7969, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7969_1 adaptiveSpanWholeCache7969_1
  · simpa only [adaptiveSpanLevel7969, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7969_2 adaptiveSpanWholeCache7969_2
  · simpa only [adaptiveSpanLevel7969, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7969_3 adaptiveSpanWholeCache7969_3
  · simpa only [adaptiveSpanLevel7969, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7969_4 adaptiveSpanWholeCache7969_4
  · simpa only [adaptiveSpanLevel7969, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7969_5 adaptiveSpanWholeCache7969_5
  · simpa only [adaptiveSpanLevel7969, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7969_6 adaptiveSpanWholeCache7969_6
  · simpa only [adaptiveSpanLevel7969, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7969_7 adaptiveSpanWholeCache7969_7
  · simpa only [adaptiveSpanLevel7969, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7969_8 adaptiveSpanWholeCache7969_8

theorem adaptiveSpanTreeRepresents7969 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes7969.length) :
    AdaptiveSpanTreeRepresents adaptiveRows7969 (halfOdds 7969)
      (sharpDegree (7245 / 2) 7 (adaptiveSpanNumerator7969 s) (adaptiveSpanDenominator7969 s))
      (sharpDegree 7245 7 (adaptiveSpanNumerator7969 s) (adaptiveSpanDenominator7969 s))
      (adaptiveSpanLevel7969 s).1 (adaptiveSpanLevel7969 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel7969, adaptiveSpanNumerator7969, adaptiveSpanDenominator7969, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3985) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid7969 adaptiveOrder7969 adaptiveSpanNumericCheck7969_0
        adaptiveSpanEven7969_0 adaptiveSpanWhole7969_0
        adaptiveSpanEvenEntries7969_0 adaptiveSpanWholeEntries7969_0
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanEvenDomain7969_0)
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanWholeDomain7969_0)
  · simpa only [adaptiveSpanLevel7969, adaptiveSpanNumerator7969, adaptiveSpanDenominator7969, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3985) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid7969 adaptiveOrder7969 adaptiveSpanNumericCheck7969_1
        adaptiveSpanEven7969_1 adaptiveSpanWhole7969_1
        adaptiveSpanEvenEntries7969_1 adaptiveSpanWholeEntries7969_1
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanEvenDomain7969_1)
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanWholeDomain7969_1)
  · simpa only [adaptiveSpanLevel7969, adaptiveSpanNumerator7969, adaptiveSpanDenominator7969, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3985) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid7969 adaptiveOrder7969 adaptiveSpanNumericCheck7969_2
        adaptiveSpanEven7969_2 adaptiveSpanWhole7969_2
        adaptiveSpanEvenEntries7969_2 adaptiveSpanWholeEntries7969_2
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanEvenDomain7969_2)
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanWholeDomain7969_2)
  · simpa only [adaptiveSpanLevel7969, adaptiveSpanNumerator7969, adaptiveSpanDenominator7969, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3985) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid7969 adaptiveOrder7969 adaptiveSpanNumericCheck7969_3
        adaptiveSpanEven7969_3 adaptiveSpanWhole7969_3
        adaptiveSpanEvenEntries7969_3 adaptiveSpanWholeEntries7969_3
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanEvenDomain7969_3)
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanWholeDomain7969_3)
  · simpa only [adaptiveSpanLevel7969, adaptiveSpanNumerator7969, adaptiveSpanDenominator7969, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3985) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid7969 adaptiveOrder7969 adaptiveSpanNumericCheck7969_4
        adaptiveSpanEven7969_4 adaptiveSpanWhole7969_4
        adaptiveSpanEvenEntries7969_4 adaptiveSpanWholeEntries7969_4
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanEvenDomain7969_4)
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanWholeDomain7969_4)
  · simpa only [adaptiveSpanLevel7969, adaptiveSpanNumerator7969, adaptiveSpanDenominator7969, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3985) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid7969 adaptiveOrder7969 adaptiveSpanNumericCheck7969_5
        adaptiveSpanEven7969_5 adaptiveSpanWhole7969_5
        adaptiveSpanEvenEntries7969_5 adaptiveSpanWholeEntries7969_5
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanEvenDomain7969_5)
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanWholeDomain7969_5)
  · simpa only [adaptiveSpanLevel7969, adaptiveSpanNumerator7969, adaptiveSpanDenominator7969, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3985) (by decide : 0 < 437)
        adaptiveSpanProfilesValid7969 adaptiveOrder7969 adaptiveSpanNumericCheck7969_6
        adaptiveSpanEven7969_6 adaptiveSpanWhole7969_6
        adaptiveSpanEvenEntries7969_6 adaptiveSpanWholeEntries7969_6
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanEvenDomain7969_6)
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanWholeDomain7969_6)
  · simpa only [adaptiveSpanLevel7969, adaptiveSpanNumerator7969, adaptiveSpanDenominator7969, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3985) (by decide : 0 < 667)
        adaptiveSpanProfilesValid7969 adaptiveOrder7969 adaptiveSpanNumericCheck7969_7
        adaptiveSpanEven7969_7 adaptiveSpanWhole7969_7
        adaptiveSpanEvenEntries7969_7 adaptiveSpanWholeEntries7969_7
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanEvenDomain7969_7)
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanWholeDomain7969_7)
  · simpa only [adaptiveSpanLevel7969, adaptiveSpanNumerator7969, adaptiveSpanDenominator7969, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3985) (by decide : 0 < 899)
        adaptiveSpanProfilesValid7969 adaptiveOrder7969 adaptiveSpanNumericCheck7969_8
        adaptiveSpanEven7969_8 adaptiveSpanWhole7969_8
        adaptiveSpanEvenEntries7969_8 adaptiveSpanWholeEntries7969_8
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanEvenDomain7969_8)
        (by rw [adaptiveSpanProfileLength7969]; exact adaptiveSpanWholeDomain7969_8)

/-- The complete finite histogram certificate for 7245 ≤ n ≤ 7969. -/
theorem adaptiveSpanHistogram7969 : DegreeIntervalCertificate 7969 adaptiveSpanPrimes7969
    (fun s v => sharpDegree (7245 / 2) 7 (adaptiveSpanNumerator7969 s)
      (adaptiveSpanDenominator7969 s) (totientDensity v))
    (fun s v => sharpDegree 7245 7 (adaptiveSpanNumerator7969 s)
      (adaptiveSpanDenominator7969 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows7969)
    adaptiveSpanPrimes7969
    (fun s => sharpDegree (7245 / 2) 7 (adaptiveSpanNumerator7969 s) (adaptiveSpanDenominator7969 s))
    (fun s => sharpDegree 7245 7 (adaptiveSpanNumerator7969 s) (adaptiveSpanDenominator7969 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid7969 adaptiveOrder7969 (coreOrderPermutationCheck_sound adaptivePermutation7969)
    (by rw [adaptiveSpanProfileLength7969]; decide +kernel)
    adaptiveSpanLevel7969 adaptiveSpanTreeCache7969 adaptiveSpanTreeRepresents7969
    (fun j => adaptiveSpanWitness7969.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck7969

/-- Every required odd cycle for a dense set, throughout 7245 ≤ n ≤ 7969. -/
theorem adaptiveSpanInterval7969 {n : ℕ} (hLn : 7245 ≤ n) (hnU : n ≤ 7969)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes7969
    adaptiveSpanNumerator7969 adaptiveSpanDenominator7969 adaptiveSpanSharpTail7969
    adaptiveSpanPrimeSupport7969 adaptiveSpanHistogram7969 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail7969
#print axioms adaptiveSpanPrimeSupport7969
#print axioms adaptiveSpanHistogram7969
#print axioms adaptiveSpanInterval7969
end Erdos883Verified
