import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate7244Metadata
import Erdos883AdaptiveSpan7244Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes7244 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator7244 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 288
  | 6 => 396
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator7244 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 323
  | 6 => 437
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail7244 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes7244.length) :
    SharpTailCertificate 7244 (adaptiveSpanPrimes7244.take s)
      (adaptiveSpanNumerator7244 s) (adaptiveSpanDenominator7244 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 7244 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7244 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7244 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7244 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7244 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7244 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7244 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7244 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 7244 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport7244 : ∀ u ∈ oddUniverse 7244,
    ∀ v ∈ oddUniverse 7244, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid7244 : AdaptiveProfileRowsValid adaptiveRows7244 :=
  coreProfileMetadataCheck_sound adaptiveMetadata7244

theorem adaptiveSpanProfileLength7244 : adaptiveRows7244.length = halfOdds 7244 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation7244)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache7244 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes7244.length) :
    (adaptiveSpanLevel7244 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel7244 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel7244, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7244_0 adaptiveSpanWholeCache7244_0
  · simpa only [adaptiveSpanLevel7244, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7244_1 adaptiveSpanWholeCache7244_1
  · simpa only [adaptiveSpanLevel7244, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7244_2 adaptiveSpanWholeCache7244_2
  · simpa only [adaptiveSpanLevel7244, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7244_3 adaptiveSpanWholeCache7244_3
  · simpa only [adaptiveSpanLevel7244, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7244_4 adaptiveSpanWholeCache7244_4
  · simpa only [adaptiveSpanLevel7244, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7244_5 adaptiveSpanWholeCache7244_5
  · simpa only [adaptiveSpanLevel7244, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7244_6 adaptiveSpanWholeCache7244_6
  · simpa only [adaptiveSpanLevel7244, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7244_7 adaptiveSpanWholeCache7244_7
  · simpa only [adaptiveSpanLevel7244, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache7244_8 adaptiveSpanWholeCache7244_8

theorem adaptiveSpanTreeRepresents7244 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes7244.length) :
    AdaptiveSpanTreeRepresents adaptiveRows7244 (halfOdds 7244)
      (sharpDegree (6586 / 2) 7 (adaptiveSpanNumerator7244 s) (adaptiveSpanDenominator7244 s))
      (sharpDegree 6586 7 (adaptiveSpanNumerator7244 s) (adaptiveSpanDenominator7244 s))
      (adaptiveSpanLevel7244 s).1 (adaptiveSpanLevel7244 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel7244, adaptiveSpanNumerator7244, adaptiveSpanDenominator7244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3622) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid7244 adaptiveOrder7244 adaptiveSpanNumericCheck7244_0
        adaptiveSpanEven7244_0 adaptiveSpanWhole7244_0
        adaptiveSpanEvenEntries7244_0 adaptiveSpanWholeEntries7244_0
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanEvenDomain7244_0)
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanWholeDomain7244_0)
  · simpa only [adaptiveSpanLevel7244, adaptiveSpanNumerator7244, adaptiveSpanDenominator7244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3622) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid7244 adaptiveOrder7244 adaptiveSpanNumericCheck7244_1
        adaptiveSpanEven7244_1 adaptiveSpanWhole7244_1
        adaptiveSpanEvenEntries7244_1 adaptiveSpanWholeEntries7244_1
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanEvenDomain7244_1)
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanWholeDomain7244_1)
  · simpa only [adaptiveSpanLevel7244, adaptiveSpanNumerator7244, adaptiveSpanDenominator7244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3622) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid7244 adaptiveOrder7244 adaptiveSpanNumericCheck7244_2
        adaptiveSpanEven7244_2 adaptiveSpanWhole7244_2
        adaptiveSpanEvenEntries7244_2 adaptiveSpanWholeEntries7244_2
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanEvenDomain7244_2)
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanWholeDomain7244_2)
  · simpa only [adaptiveSpanLevel7244, adaptiveSpanNumerator7244, adaptiveSpanDenominator7244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3622) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid7244 adaptiveOrder7244 adaptiveSpanNumericCheck7244_3
        adaptiveSpanEven7244_3 adaptiveSpanWhole7244_3
        adaptiveSpanEvenEntries7244_3 adaptiveSpanWholeEntries7244_3
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanEvenDomain7244_3)
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanWholeDomain7244_3)
  · simpa only [adaptiveSpanLevel7244, adaptiveSpanNumerator7244, adaptiveSpanDenominator7244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3622) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid7244 adaptiveOrder7244 adaptiveSpanNumericCheck7244_4
        adaptiveSpanEven7244_4 adaptiveSpanWhole7244_4
        adaptiveSpanEvenEntries7244_4 adaptiveSpanWholeEntries7244_4
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanEvenDomain7244_4)
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanWholeDomain7244_4)
  · simpa only [adaptiveSpanLevel7244, adaptiveSpanNumerator7244, adaptiveSpanDenominator7244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3622) (by decide : 0 < 323)
        adaptiveSpanProfilesValid7244 adaptiveOrder7244 adaptiveSpanNumericCheck7244_5
        adaptiveSpanEven7244_5 adaptiveSpanWhole7244_5
        adaptiveSpanEvenEntries7244_5 adaptiveSpanWholeEntries7244_5
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanEvenDomain7244_5)
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanWholeDomain7244_5)
  · simpa only [adaptiveSpanLevel7244, adaptiveSpanNumerator7244, adaptiveSpanDenominator7244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3622) (by decide : 0 < 437)
        adaptiveSpanProfilesValid7244 adaptiveOrder7244 adaptiveSpanNumericCheck7244_6
        adaptiveSpanEven7244_6 adaptiveSpanWhole7244_6
        adaptiveSpanEvenEntries7244_6 adaptiveSpanWholeEntries7244_6
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanEvenDomain7244_6)
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanWholeDomain7244_6)
  · simpa only [adaptiveSpanLevel7244, adaptiveSpanNumerator7244, adaptiveSpanDenominator7244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3622) (by decide : 0 < 667)
        adaptiveSpanProfilesValid7244 adaptiveOrder7244 adaptiveSpanNumericCheck7244_7
        adaptiveSpanEven7244_7 adaptiveSpanWhole7244_7
        adaptiveSpanEvenEntries7244_7 adaptiveSpanWholeEntries7244_7
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanEvenDomain7244_7)
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanWholeDomain7244_7)
  · simpa only [adaptiveSpanLevel7244, adaptiveSpanNumerator7244, adaptiveSpanDenominator7244, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 3622) (by decide : 0 < 899)
        adaptiveSpanProfilesValid7244 adaptiveOrder7244 adaptiveSpanNumericCheck7244_8
        adaptiveSpanEven7244_8 adaptiveSpanWhole7244_8
        adaptiveSpanEvenEntries7244_8 adaptiveSpanWholeEntries7244_8
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanEvenDomain7244_8)
        (by rw [adaptiveSpanProfileLength7244]; exact adaptiveSpanWholeDomain7244_8)

/-- The complete finite histogram certificate for 6586 ≤ n ≤ 7244. -/
theorem adaptiveSpanHistogram7244 : DegreeIntervalCertificate 7244 adaptiveSpanPrimes7244
    (fun s v => sharpDegree (6586 / 2) 7 (adaptiveSpanNumerator7244 s)
      (adaptiveSpanDenominator7244 s) (totientDensity v))
    (fun s v => sharpDegree 6586 7 (adaptiveSpanNumerator7244 s)
      (adaptiveSpanDenominator7244 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows7244)
    adaptiveSpanPrimes7244
    (fun s => sharpDegree (6586 / 2) 7 (adaptiveSpanNumerator7244 s) (adaptiveSpanDenominator7244 s))
    (fun s => sharpDegree 6586 7 (adaptiveSpanNumerator7244 s) (adaptiveSpanDenominator7244 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid7244 adaptiveOrder7244 (coreOrderPermutationCheck_sound adaptivePermutation7244)
    (by rw [adaptiveSpanProfileLength7244]; decide +kernel)
    adaptiveSpanLevel7244 adaptiveSpanTreeCache7244 adaptiveSpanTreeRepresents7244
    (fun j => adaptiveSpanWitness7244.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck7244

/-- Every required odd cycle for a dense set, throughout 6586 ≤ n ≤ 7244. -/
theorem adaptiveSpanInterval7244 {n : ℕ} (hLn : 6586 ≤ n) (hnU : n ≤ 7244)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes7244
    adaptiveSpanNumerator7244 adaptiveSpanDenominator7244 adaptiveSpanSharpTail7244
    adaptiveSpanPrimeSupport7244 adaptiveSpanHistogram7244 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail7244
#print axioms adaptiveSpanPrimeSupport7244
#print axioms adaptiveSpanHistogram7244
#print axioms adaptiveSpanInterval7244
end Erdos883Verified
