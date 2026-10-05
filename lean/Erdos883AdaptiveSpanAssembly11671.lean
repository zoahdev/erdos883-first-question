import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate11671Metadata
import Erdos883AdaptiveSpan11671Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate11671PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes11671 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator11671 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 396
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator11671 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 437
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail11671 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes11671.length) :
    SharpTailCertificate 11671 (adaptiveSpanPrimes11671.take s)
      (adaptiveSpanNumerator11671 s) (adaptiveSpanDenominator11671 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 11671 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 11671 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 11671 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 11671 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 11671 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 11671 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 11671 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 11671 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 11671 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport11671 : ∀ u ∈ oddUniverse 11671,
    ∀ v ∈ oddUniverse 11671, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid11671 : AdaptiveProfileRowsValid adaptiveRows11671 :=
  coreProfileMetadataCheck_sound adaptiveMetadata11671

theorem adaptiveSpanProfileLength11671 : adaptiveRows11671.length = halfOdds 11671 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics11671
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache11671 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes11671.length) :
    (adaptiveSpanLevel11671 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel11671 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel11671, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache11671_0 adaptiveSpanWholeCache11671_0
  · simpa only [adaptiveSpanLevel11671, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache11671_1 adaptiveSpanWholeCache11671_1
  · simpa only [adaptiveSpanLevel11671, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache11671_2 adaptiveSpanWholeCache11671_2
  · simpa only [adaptiveSpanLevel11671, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache11671_3 adaptiveSpanWholeCache11671_3
  · simpa only [adaptiveSpanLevel11671, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache11671_4 adaptiveSpanWholeCache11671_4
  · simpa only [adaptiveSpanLevel11671, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache11671_5 adaptiveSpanWholeCache11671_5
  · simpa only [adaptiveSpanLevel11671, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache11671_6 adaptiveSpanWholeCache11671_6
  · simpa only [adaptiveSpanLevel11671, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache11671_7 adaptiveSpanWholeCache11671_7
  · simpa only [adaptiveSpanLevel11671, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache11671_8 adaptiveSpanWholeCache11671_8

theorem adaptiveSpanTreeRepresents11671 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes11671.length) :
    AdaptiveSpanTreeRepresents adaptiveRows11671 (halfOdds 11671)
      (sharpDegree (10610 / 2) 8 (adaptiveSpanNumerator11671 s) (adaptiveSpanDenominator11671 s))
      (sharpDegree 10610 8 (adaptiveSpanNumerator11671 s) (adaptiveSpanDenominator11671 s))
      (adaptiveSpanLevel11671 s).1 (adaptiveSpanLevel11671 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel11671, adaptiveSpanNumerator11671, adaptiveSpanDenominator11671, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5836) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid11671 adaptiveOrder11671 adaptiveSpanNumericCheck11671_0
        adaptiveSpanEven11671_0 adaptiveSpanWhole11671_0
        adaptiveSpanEvenEntries11671_0 adaptiveSpanWholeEntries11671_0
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanEvenDomain11671_0)
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanWholeDomain11671_0)
  · simpa only [adaptiveSpanLevel11671, adaptiveSpanNumerator11671, adaptiveSpanDenominator11671, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5836) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid11671 adaptiveOrder11671 adaptiveSpanNumericCheck11671_1
        adaptiveSpanEven11671_1 adaptiveSpanWhole11671_1
        adaptiveSpanEvenEntries11671_1 adaptiveSpanWholeEntries11671_1
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanEvenDomain11671_1)
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanWholeDomain11671_1)
  · simpa only [adaptiveSpanLevel11671, adaptiveSpanNumerator11671, adaptiveSpanDenominator11671, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5836) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid11671 adaptiveOrder11671 adaptiveSpanNumericCheck11671_2
        adaptiveSpanEven11671_2 adaptiveSpanWhole11671_2
        adaptiveSpanEvenEntries11671_2 adaptiveSpanWholeEntries11671_2
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanEvenDomain11671_2)
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanWholeDomain11671_2)
  · simpa only [adaptiveSpanLevel11671, adaptiveSpanNumerator11671, adaptiveSpanDenominator11671, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5836) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid11671 adaptiveOrder11671 adaptiveSpanNumericCheck11671_3
        adaptiveSpanEven11671_3 adaptiveSpanWhole11671_3
        adaptiveSpanEvenEntries11671_3 adaptiveSpanWholeEntries11671_3
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanEvenDomain11671_3)
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanWholeDomain11671_3)
  · simpa only [adaptiveSpanLevel11671, adaptiveSpanNumerator11671, adaptiveSpanDenominator11671, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5836) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid11671 adaptiveOrder11671 adaptiveSpanNumericCheck11671_4
        adaptiveSpanEven11671_4 adaptiveSpanWhole11671_4
        adaptiveSpanEvenEntries11671_4 adaptiveSpanWholeEntries11671_4
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanEvenDomain11671_4)
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanWholeDomain11671_4)
  · simpa only [adaptiveSpanLevel11671, adaptiveSpanNumerator11671, adaptiveSpanDenominator11671, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5836) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid11671 adaptiveOrder11671 adaptiveSpanNumericCheck11671_5
        adaptiveSpanEven11671_5 adaptiveSpanWhole11671_5
        adaptiveSpanEvenEntries11671_5 adaptiveSpanWholeEntries11671_5
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanEvenDomain11671_5)
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanWholeDomain11671_5)
  · simpa only [adaptiveSpanLevel11671, adaptiveSpanNumerator11671, adaptiveSpanDenominator11671, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5836) (by decide : 0 < 437)
        adaptiveSpanProfilesValid11671 adaptiveOrder11671 adaptiveSpanNumericCheck11671_6
        adaptiveSpanEven11671_6 adaptiveSpanWhole11671_6
        adaptiveSpanEvenEntries11671_6 adaptiveSpanWholeEntries11671_6
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanEvenDomain11671_6)
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanWholeDomain11671_6)
  · simpa only [adaptiveSpanLevel11671, adaptiveSpanNumerator11671, adaptiveSpanDenominator11671, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5836) (by decide : 0 < 667)
        adaptiveSpanProfilesValid11671 adaptiveOrder11671 adaptiveSpanNumericCheck11671_7
        adaptiveSpanEven11671_7 adaptiveSpanWhole11671_7
        adaptiveSpanEvenEntries11671_7 adaptiveSpanWholeEntries11671_7
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanEvenDomain11671_7)
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanWholeDomain11671_7)
  · simpa only [adaptiveSpanLevel11671, adaptiveSpanNumerator11671, adaptiveSpanDenominator11671, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 5836) (by decide : 0 < 899)
        adaptiveSpanProfilesValid11671 adaptiveOrder11671 adaptiveSpanNumericCheck11671_8
        adaptiveSpanEven11671_8 adaptiveSpanWhole11671_8
        adaptiveSpanEvenEntries11671_8 adaptiveSpanWholeEntries11671_8
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanEvenDomain11671_8)
        (by rw [adaptiveSpanProfileLength11671]; exact adaptiveSpanWholeDomain11671_8)

/-- The complete finite histogram certificate for 10610 ≤ n ≤ 11671. -/
theorem adaptiveSpanHistogram11671 : DegreeIntervalCertificate 11671 adaptiveSpanPrimes11671
    (fun s v => sharpDegree (10610 / 2) 8 (adaptiveSpanNumerator11671 s)
      (adaptiveSpanDenominator11671 s) (totientDensity v))
    (fun s v => sharpDegree 10610 8 (adaptiveSpanNumerator11671 s)
      (adaptiveSpanDenominator11671 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows11671)
    adaptiveSpanPrimes11671
    (fun s => sharpDegree (10610 / 2) 8 (adaptiveSpanNumerator11671 s) (adaptiveSpanDenominator11671 s))
    (fun s => sharpDegree 10610 8 (adaptiveSpanNumerator11671 s) (adaptiveSpanDenominator11671 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid11671 adaptiveOrder11671 adaptivePermutationSemantics11671
    (by rw [adaptiveSpanProfileLength11671]; decide +kernel)
    adaptiveSpanLevel11671 adaptiveSpanTreeCache11671 adaptiveSpanTreeRepresents11671
    (fun j => adaptiveSpanWitness11671.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength11671
  · exact adaptiveSpanWitnessCheck11671

/-- Every required odd cycle for a dense set, throughout 10610 ≤ n ≤ 11671. -/
theorem adaptiveSpanInterval11671 {n : ℕ} (hLn : 10610 ≤ n) (hnU : n ≤ 11671)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes11671
    adaptiveSpanNumerator11671 adaptiveSpanDenominator11671 adaptiveSpanSharpTail11671
    adaptiveSpanPrimeSupport11671 adaptiveSpanHistogram11671 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail11671
#print axioms adaptiveSpanPrimeSupport11671
#print axioms adaptiveSpanHistogram11671
#print axioms adaptiveSpanInterval11671
end Erdos883Verified
