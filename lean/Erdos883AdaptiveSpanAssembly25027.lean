import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate25027Metadata
import Erdos883AdaptiveSpan25027Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate25027PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes25027 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator25027 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 840

def adaptiveSpanDenominator25027 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 899

theorem adaptiveSpanSharpTail25027 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes25027.length) :
    SharpTailCertificate 25027 (adaptiveSpanPrimes25027.take s)
      (adaptiveSpanNumerator25027 s) (adaptiveSpanDenominator25027 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 25027 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 25027 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 25027 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 25027 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 25027 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 25027 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 25027 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 25027 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 25027 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport25027 : ∀ u ∈ oddUniverse 25027,
    ∀ v ∈ oddUniverse 25027, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid25027 : AdaptiveProfileRowsValid adaptiveRows25027 :=
  coreProfileMetadataCheck_sound adaptiveMetadata25027

theorem adaptiveSpanProfileLength25027 : adaptiveRows25027.length = halfOdds 25027 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics25027
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache25027 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes25027.length) :
    (adaptiveSpanLevel25027 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel25027 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel25027, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache25027_0 adaptiveSpanWholeCache25027_0
  · simpa only [adaptiveSpanLevel25027, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache25027_1 adaptiveSpanWholeCache25027_1
  · simpa only [adaptiveSpanLevel25027, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache25027_2 adaptiveSpanWholeCache25027_2
  · simpa only [adaptiveSpanLevel25027, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache25027_3 adaptiveSpanWholeCache25027_3
  · simpa only [adaptiveSpanLevel25027, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache25027_4 adaptiveSpanWholeCache25027_4
  · simpa only [adaptiveSpanLevel25027, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache25027_5 adaptiveSpanWholeCache25027_5
  · simpa only [adaptiveSpanLevel25027, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache25027_6 adaptiveSpanWholeCache25027_6
  · simpa only [adaptiveSpanLevel25027, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache25027_7 adaptiveSpanWholeCache25027_7
  · simpa only [adaptiveSpanLevel25027, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache25027_8 adaptiveSpanWholeCache25027_8

theorem adaptiveSpanTreeRepresents25027 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes25027.length) :
    AdaptiveSpanTreeRepresents adaptiveRows25027 (halfOdds 25027)
      (sharpDegree (22752 / 2) 8 (adaptiveSpanNumerator25027 s) (adaptiveSpanDenominator25027 s))
      (sharpDegree 22752 8 (adaptiveSpanNumerator25027 s) (adaptiveSpanDenominator25027 s))
      (adaptiveSpanLevel25027 s).1 (adaptiveSpanLevel25027 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel25027, adaptiveSpanNumerator25027, adaptiveSpanDenominator25027, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 12514) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid25027 adaptiveOrder25027 adaptiveSpanNumericCheck25027_0
        adaptiveSpanEven25027_0 adaptiveSpanWhole25027_0
        adaptiveSpanEvenEntries25027_0 adaptiveSpanWholeEntries25027_0
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanEvenDomain25027_0)
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanWholeDomain25027_0)
  · simpa only [adaptiveSpanLevel25027, adaptiveSpanNumerator25027, adaptiveSpanDenominator25027, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 12514) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid25027 adaptiveOrder25027 adaptiveSpanNumericCheck25027_1
        adaptiveSpanEven25027_1 adaptiveSpanWhole25027_1
        adaptiveSpanEvenEntries25027_1 adaptiveSpanWholeEntries25027_1
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanEvenDomain25027_1)
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanWholeDomain25027_1)
  · simpa only [adaptiveSpanLevel25027, adaptiveSpanNumerator25027, adaptiveSpanDenominator25027, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 12514) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid25027 adaptiveOrder25027 adaptiveSpanNumericCheck25027_2
        adaptiveSpanEven25027_2 adaptiveSpanWhole25027_2
        adaptiveSpanEvenEntries25027_2 adaptiveSpanWholeEntries25027_2
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanEvenDomain25027_2)
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanWholeDomain25027_2)
  · simpa only [adaptiveSpanLevel25027, adaptiveSpanNumerator25027, adaptiveSpanDenominator25027, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 12514) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid25027 adaptiveOrder25027 adaptiveSpanNumericCheck25027_3
        adaptiveSpanEven25027_3 adaptiveSpanWhole25027_3
        adaptiveSpanEvenEntries25027_3 adaptiveSpanWholeEntries25027_3
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanEvenDomain25027_3)
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanWholeDomain25027_3)
  · simpa only [adaptiveSpanLevel25027, adaptiveSpanNumerator25027, adaptiveSpanDenominator25027, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 12514) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid25027 adaptiveOrder25027 adaptiveSpanNumericCheck25027_4
        adaptiveSpanEven25027_4 adaptiveSpanWhole25027_4
        adaptiveSpanEvenEntries25027_4 adaptiveSpanWholeEntries25027_4
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanEvenDomain25027_4)
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanWholeDomain25027_4)
  · simpa only [adaptiveSpanLevel25027, adaptiveSpanNumerator25027, adaptiveSpanDenominator25027, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 12514) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid25027 adaptiveOrder25027 adaptiveSpanNumericCheck25027_5
        adaptiveSpanEven25027_5 adaptiveSpanWhole25027_5
        adaptiveSpanEvenEntries25027_5 adaptiveSpanWholeEntries25027_5
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanEvenDomain25027_5)
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanWholeDomain25027_5)
  · simpa only [adaptiveSpanLevel25027, adaptiveSpanNumerator25027, adaptiveSpanDenominator25027, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 12514) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid25027 adaptiveOrder25027 adaptiveSpanNumericCheck25027_6
        adaptiveSpanEven25027_6 adaptiveSpanWhole25027_6
        adaptiveSpanEvenEntries25027_6 adaptiveSpanWholeEntries25027_6
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanEvenDomain25027_6)
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanWholeDomain25027_6)
  · simpa only [adaptiveSpanLevel25027, adaptiveSpanNumerator25027, adaptiveSpanDenominator25027, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 12514) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid25027 adaptiveOrder25027 adaptiveSpanNumericCheck25027_7
        adaptiveSpanEven25027_7 adaptiveSpanWhole25027_7
        adaptiveSpanEvenEntries25027_7 adaptiveSpanWholeEntries25027_7
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanEvenDomain25027_7)
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanWholeDomain25027_7)
  · simpa only [adaptiveSpanLevel25027, adaptiveSpanNumerator25027, adaptiveSpanDenominator25027, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 12514) (by decide : 0 < 899)
        adaptiveSpanProfilesValid25027 adaptiveOrder25027 adaptiveSpanNumericCheck25027_8
        adaptiveSpanEven25027_8 adaptiveSpanWhole25027_8
        adaptiveSpanEvenEntries25027_8 adaptiveSpanWholeEntries25027_8
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanEvenDomain25027_8)
        (by rw [adaptiveSpanProfileLength25027]; exact adaptiveSpanWholeDomain25027_8)

/-- The complete finite histogram certificate for 22752 ≤ n ≤ 25027. -/
theorem adaptiveSpanHistogram25027 : DegreeIntervalCertificate 25027 adaptiveSpanPrimes25027
    (fun s v => sharpDegree (22752 / 2) 8 (adaptiveSpanNumerator25027 s)
      (adaptiveSpanDenominator25027 s) (totientDensity v))
    (fun s v => sharpDegree 22752 8 (adaptiveSpanNumerator25027 s)
      (adaptiveSpanDenominator25027 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows25027)
    adaptiveSpanPrimes25027
    (fun s => sharpDegree (22752 / 2) 8 (adaptiveSpanNumerator25027 s) (adaptiveSpanDenominator25027 s))
    (fun s => sharpDegree 22752 8 (adaptiveSpanNumerator25027 s) (adaptiveSpanDenominator25027 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid25027 adaptiveOrder25027 adaptivePermutationSemantics25027
    (by rw [adaptiveSpanProfileLength25027]; decide +kernel)
    adaptiveSpanLevel25027 adaptiveSpanTreeCache25027 adaptiveSpanTreeRepresents25027
    (fun j => adaptiveSpanWitness25027.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength25027
  · exact adaptiveSpanWitnessCheck25027

/-- Every required odd cycle for a dense set, throughout 22752 ≤ n ≤ 25027. -/
theorem adaptiveSpanInterval25027 {n : ℕ} (hLn : 22752 ≤ n) (hnU : n ≤ 25027)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes25027
    adaptiveSpanNumerator25027 adaptiveSpanDenominator25027 adaptiveSpanSharpTail25027
    adaptiveSpanPrimeSupport25027 adaptiveSpanHistogram25027 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail25027
#print axioms adaptiveSpanPrimeSupport25027
#print axioms adaptiveSpanHistogram25027
#print axioms adaptiveSpanInterval25027
end Erdos883Verified
