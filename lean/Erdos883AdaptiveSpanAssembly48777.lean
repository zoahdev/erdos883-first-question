import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate48777Metadata
import Erdos883AdaptiveSpan48777Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate48777PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes48777 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator48777 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 34560
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator48777 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 46189
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail48777 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes48777.length) :
    SharpTailCertificate 48777 (adaptiveSpanPrimes48777.take s)
      (adaptiveSpanNumerator48777 s) (adaptiveSpanDenominator48777 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 48777 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 48777 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 48777 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 48777 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 48777 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 48777 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 48777 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 48777 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 48777 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport48777 : ∀ u ∈ oddUniverse 48777,
    ∀ v ∈ oddUniverse 48777, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid48777 : AdaptiveProfileRowsValid adaptiveRows48777 :=
  coreProfileMetadataCheck_sound adaptiveMetadata48777

theorem adaptiveSpanProfileLength48777 : adaptiveRows48777.length = halfOdds 48777 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics48777
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache48777 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes48777.length) :
    (adaptiveSpanLevel48777 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel48777 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel48777, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache48777_0 adaptiveSpanWholeCache48777_0
  · simpa only [adaptiveSpanLevel48777, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache48777_1 adaptiveSpanWholeCache48777_1
  · simpa only [adaptiveSpanLevel48777, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache48777_2 adaptiveSpanWholeCache48777_2
  · simpa only [adaptiveSpanLevel48777, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache48777_3 adaptiveSpanWholeCache48777_3
  · simpa only [adaptiveSpanLevel48777, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache48777_4 adaptiveSpanWholeCache48777_4
  · simpa only [adaptiveSpanLevel48777, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache48777_5 adaptiveSpanWholeCache48777_5
  · simpa only [adaptiveSpanLevel48777, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache48777_6 adaptiveSpanWholeCache48777_6
  · simpa only [adaptiveSpanLevel48777, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache48777_7 adaptiveSpanWholeCache48777_7
  · simpa only [adaptiveSpanLevel48777, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache48777_8 adaptiveSpanWholeCache48777_8

theorem adaptiveSpanTreeRepresents48777 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes48777.length) :
    AdaptiveSpanTreeRepresents adaptiveRows48777 (halfOdds 48777)
      (sharpDegree (44343 / 2) 8 (adaptiveSpanNumerator48777 s) (adaptiveSpanDenominator48777 s))
      (sharpDegree 44343 8 (adaptiveSpanNumerator48777 s) (adaptiveSpanDenominator48777 s))
      (adaptiveSpanLevel48777 s).1 (adaptiveSpanLevel48777 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel48777, adaptiveSpanNumerator48777, adaptiveSpanDenominator48777, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 24389) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid48777 adaptiveOrder48777 adaptiveSpanNumericCheck48777_0
        adaptiveSpanEven48777_0 adaptiveSpanWhole48777_0
        adaptiveSpanEvenEntries48777_0 adaptiveSpanWholeEntries48777_0
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanEvenDomain48777_0)
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanWholeDomain48777_0)
  · simpa only [adaptiveSpanLevel48777, adaptiveSpanNumerator48777, adaptiveSpanDenominator48777, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 24389) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid48777 adaptiveOrder48777 adaptiveSpanNumericCheck48777_1
        adaptiveSpanEven48777_1 adaptiveSpanWhole48777_1
        adaptiveSpanEvenEntries48777_1 adaptiveSpanWholeEntries48777_1
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanEvenDomain48777_1)
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanWholeDomain48777_1)
  · simpa only [adaptiveSpanLevel48777, adaptiveSpanNumerator48777, adaptiveSpanDenominator48777, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 24389) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid48777 adaptiveOrder48777 adaptiveSpanNumericCheck48777_2
        adaptiveSpanEven48777_2 adaptiveSpanWhole48777_2
        adaptiveSpanEvenEntries48777_2 adaptiveSpanWholeEntries48777_2
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanEvenDomain48777_2)
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanWholeDomain48777_2)
  · simpa only [adaptiveSpanLevel48777, adaptiveSpanNumerator48777, adaptiveSpanDenominator48777, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 24389) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid48777 adaptiveOrder48777 adaptiveSpanNumericCheck48777_3
        adaptiveSpanEven48777_3 adaptiveSpanWhole48777_3
        adaptiveSpanEvenEntries48777_3 adaptiveSpanWholeEntries48777_3
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanEvenDomain48777_3)
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanWholeDomain48777_3)
  · simpa only [adaptiveSpanLevel48777, adaptiveSpanNumerator48777, adaptiveSpanDenominator48777, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 24389) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid48777 adaptiveOrder48777 adaptiveSpanNumericCheck48777_4
        adaptiveSpanEven48777_4 adaptiveSpanWhole48777_4
        adaptiveSpanEvenEntries48777_4 adaptiveSpanWholeEntries48777_4
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanEvenDomain48777_4)
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanWholeDomain48777_4)
  · simpa only [adaptiveSpanLevel48777, adaptiveSpanNumerator48777, adaptiveSpanDenominator48777, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 24389) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid48777 adaptiveOrder48777 adaptiveSpanNumericCheck48777_5
        adaptiveSpanEven48777_5 adaptiveSpanWhole48777_5
        adaptiveSpanEvenEntries48777_5 adaptiveSpanWholeEntries48777_5
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanEvenDomain48777_5)
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanWholeDomain48777_5)
  · simpa only [adaptiveSpanLevel48777, adaptiveSpanNumerator48777, adaptiveSpanDenominator48777, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 24389) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid48777 adaptiveOrder48777 adaptiveSpanNumericCheck48777_6
        adaptiveSpanEven48777_6 adaptiveSpanWhole48777_6
        adaptiveSpanEvenEntries48777_6 adaptiveSpanWholeEntries48777_6
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanEvenDomain48777_6)
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanWholeDomain48777_6)
  · simpa only [adaptiveSpanLevel48777, adaptiveSpanNumerator48777, adaptiveSpanDenominator48777, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 24389) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid48777 adaptiveOrder48777 adaptiveSpanNumericCheck48777_7
        adaptiveSpanEven48777_7 adaptiveSpanWhole48777_7
        adaptiveSpanEvenEntries48777_7 adaptiveSpanWholeEntries48777_7
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanEvenDomain48777_7)
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanWholeDomain48777_7)
  · simpa only [adaptiveSpanLevel48777, adaptiveSpanNumerator48777, adaptiveSpanDenominator48777, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 24389) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid48777 adaptiveOrder48777 adaptiveSpanNumericCheck48777_8
        adaptiveSpanEven48777_8 adaptiveSpanWhole48777_8
        adaptiveSpanEvenEntries48777_8 adaptiveSpanWholeEntries48777_8
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanEvenDomain48777_8)
        (by rw [adaptiveSpanProfileLength48777]; exact adaptiveSpanWholeDomain48777_8)

/-- The complete finite histogram certificate for 44343 ≤ n ≤ 48777. -/
theorem adaptiveSpanHistogram48777 : DegreeIntervalCertificate 48777 adaptiveSpanPrimes48777
    (fun s v => sharpDegree (44343 / 2) 8 (adaptiveSpanNumerator48777 s)
      (adaptiveSpanDenominator48777 s) (totientDensity v))
    (fun s v => sharpDegree 44343 8 (adaptiveSpanNumerator48777 s)
      (adaptiveSpanDenominator48777 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows48777)
    adaptiveSpanPrimes48777
    (fun s => sharpDegree (44343 / 2) 8 (adaptiveSpanNumerator48777 s) (adaptiveSpanDenominator48777 s))
    (fun s => sharpDegree 44343 8 (adaptiveSpanNumerator48777 s) (adaptiveSpanDenominator48777 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid48777 adaptiveOrder48777 adaptivePermutationSemantics48777
    (by rw [adaptiveSpanProfileLength48777]; decide +kernel)
    adaptiveSpanLevel48777 adaptiveSpanTreeCache48777 adaptiveSpanTreeRepresents48777
    (fun j => adaptiveSpanWitness48777.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength48777
  · exact adaptiveSpanWitnessCheck48777

/-- Every required odd cycle for a dense set, throughout 44343 ≤ n ≤ 48777. -/
theorem adaptiveSpanInterval48777 {n : ℕ} (hLn : 44343 ≤ n) (hnU : n ≤ 48777)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes48777
    adaptiveSpanNumerator48777 adaptiveSpanDenominator48777 adaptiveSpanSharpTail48777
    adaptiveSpanPrimeSupport48777 adaptiveSpanHistogram48777 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail48777
#print axioms adaptiveSpanPrimeSupport48777
#print axioms adaptiveSpanHistogram48777
#print axioms adaptiveSpanInterval48777
end Erdos883Verified
