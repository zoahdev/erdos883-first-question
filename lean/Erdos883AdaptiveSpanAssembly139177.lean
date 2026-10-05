import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate139177Metadata
import Erdos883AdaptiveSpan139177Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate139177PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes139177 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator139177 : ℕ → ℕ
  | 0 => 5760
  | 1 => 46080
  | 2 => 11520
  | 3 => 34560
  | 4 => 76032
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator139177 : ℕ → ℕ
  | 0 => 15015
  | 1 => 85085
  | 2 => 17017
  | 3 => 46189
  | 4 => 96577
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail139177 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes139177.length) :
    SharpTailCertificate 139177 (adaptiveSpanPrimes139177.take s)
      (adaptiveSpanNumerator139177 s) (adaptiveSpanDenominator139177 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 139177 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 139177 [3] 46080 85085
    refine ⟨by decide, {5, 7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 139177 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 139177 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 139177 [3, 5, 7, 11] 76032 96577
    refine ⟨by decide, {13, 17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 139177 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 139177 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 139177 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 139177 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport139177 : ∀ u ∈ oddUniverse 139177,
    ∀ v ∈ oddUniverse 139177, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid139177 : AdaptiveProfileRowsValid adaptiveRows139177 :=
  coreProfileMetadataCheck_sound adaptiveMetadata139177

theorem adaptiveSpanProfileLength139177 : adaptiveRows139177.length = halfOdds 139177 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics139177
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache139177 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes139177.length) :
    (adaptiveSpanLevel139177 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel139177 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel139177, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache139177_0 adaptiveSpanWholeCache139177_0
  · simpa only [adaptiveSpanLevel139177, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache139177_1 adaptiveSpanWholeCache139177_1
  · simpa only [adaptiveSpanLevel139177, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache139177_2 adaptiveSpanWholeCache139177_2
  · simpa only [adaptiveSpanLevel139177, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache139177_3 adaptiveSpanWholeCache139177_3
  · simpa only [adaptiveSpanLevel139177, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache139177_4 adaptiveSpanWholeCache139177_4
  · simpa only [adaptiveSpanLevel139177, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache139177_5 adaptiveSpanWholeCache139177_5
  · simpa only [adaptiveSpanLevel139177, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache139177_6 adaptiveSpanWholeCache139177_6
  · simpa only [adaptiveSpanLevel139177, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache139177_7 adaptiveSpanWholeCache139177_7
  · simpa only [adaptiveSpanLevel139177, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache139177_8 adaptiveSpanWholeCache139177_8

theorem adaptiveSpanTreeRepresents139177 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes139177.length) :
    AdaptiveSpanTreeRepresents adaptiveRows139177 (halfOdds 139177)
      (sharpDegree (126525 / 2) 9 (adaptiveSpanNumerator139177 s) (adaptiveSpanDenominator139177 s))
      (sharpDegree 126525 9 (adaptiveSpanNumerator139177 s) (adaptiveSpanDenominator139177 s))
      (adaptiveSpanLevel139177 s).1 (adaptiveSpanLevel139177 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel139177, adaptiveSpanNumerator139177, adaptiveSpanDenominator139177, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 69589) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid139177 adaptiveOrder139177 adaptiveSpanNumericCheck139177_0
        adaptiveSpanEven139177_0 adaptiveSpanWhole139177_0
        adaptiveSpanEvenEntries139177_0 adaptiveSpanWholeEntries139177_0
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanEvenDomain139177_0)
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanWholeDomain139177_0)
  · simpa only [adaptiveSpanLevel139177, adaptiveSpanNumerator139177, adaptiveSpanDenominator139177, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 69589) (by decide : 0 < 85085)
        adaptiveSpanProfilesValid139177 adaptiveOrder139177 adaptiveSpanNumericCheck139177_1
        adaptiveSpanEven139177_1 adaptiveSpanWhole139177_1
        adaptiveSpanEvenEntries139177_1 adaptiveSpanWholeEntries139177_1
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanEvenDomain139177_1)
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanWholeDomain139177_1)
  · simpa only [adaptiveSpanLevel139177, adaptiveSpanNumerator139177, adaptiveSpanDenominator139177, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 69589) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid139177 adaptiveOrder139177 adaptiveSpanNumericCheck139177_2
        adaptiveSpanEven139177_2 adaptiveSpanWhole139177_2
        adaptiveSpanEvenEntries139177_2 adaptiveSpanWholeEntries139177_2
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanEvenDomain139177_2)
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanWholeDomain139177_2)
  · simpa only [adaptiveSpanLevel139177, adaptiveSpanNumerator139177, adaptiveSpanDenominator139177, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 69589) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid139177 adaptiveOrder139177 adaptiveSpanNumericCheck139177_3
        adaptiveSpanEven139177_3 adaptiveSpanWhole139177_3
        adaptiveSpanEvenEntries139177_3 adaptiveSpanWholeEntries139177_3
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanEvenDomain139177_3)
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanWholeDomain139177_3)
  · simpa only [adaptiveSpanLevel139177, adaptiveSpanNumerator139177, adaptiveSpanDenominator139177, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 69589) (by decide : 0 < 96577)
        adaptiveSpanProfilesValid139177 adaptiveOrder139177 adaptiveSpanNumericCheck139177_4
        adaptiveSpanEven139177_4 adaptiveSpanWhole139177_4
        adaptiveSpanEvenEntries139177_4 adaptiveSpanWholeEntries139177_4
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanEvenDomain139177_4)
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanWholeDomain139177_4)
  · simpa only [adaptiveSpanLevel139177, adaptiveSpanNumerator139177, adaptiveSpanDenominator139177, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 69589) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid139177 adaptiveOrder139177 adaptiveSpanNumericCheck139177_5
        adaptiveSpanEven139177_5 adaptiveSpanWhole139177_5
        adaptiveSpanEvenEntries139177_5 adaptiveSpanWholeEntries139177_5
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanEvenDomain139177_5)
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanWholeDomain139177_5)
  · simpa only [adaptiveSpanLevel139177, adaptiveSpanNumerator139177, adaptiveSpanDenominator139177, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 69589) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid139177 adaptiveOrder139177 adaptiveSpanNumericCheck139177_6
        adaptiveSpanEven139177_6 adaptiveSpanWhole139177_6
        adaptiveSpanEvenEntries139177_6 adaptiveSpanWholeEntries139177_6
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanEvenDomain139177_6)
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanWholeDomain139177_6)
  · simpa only [adaptiveSpanLevel139177, adaptiveSpanNumerator139177, adaptiveSpanDenominator139177, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 69589) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid139177 adaptiveOrder139177 adaptiveSpanNumericCheck139177_7
        adaptiveSpanEven139177_7 adaptiveSpanWhole139177_7
        adaptiveSpanEvenEntries139177_7 adaptiveSpanWholeEntries139177_7
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanEvenDomain139177_7)
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanWholeDomain139177_7)
  · simpa only [adaptiveSpanLevel139177, adaptiveSpanNumerator139177, adaptiveSpanDenominator139177, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 69589) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid139177 adaptiveOrder139177 adaptiveSpanNumericCheck139177_8
        adaptiveSpanEven139177_8 adaptiveSpanWhole139177_8
        adaptiveSpanEvenEntries139177_8 adaptiveSpanWholeEntries139177_8
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanEvenDomain139177_8)
        (by rw [adaptiveSpanProfileLength139177]; exact adaptiveSpanWholeDomain139177_8)

/-- The complete finite histogram certificate for 126525 ≤ n ≤ 139177. -/
theorem adaptiveSpanHistogram139177 : DegreeIntervalCertificate 139177 adaptiveSpanPrimes139177
    (fun s v => sharpDegree (126525 / 2) 9 (adaptiveSpanNumerator139177 s)
      (adaptiveSpanDenominator139177 s) (totientDensity v))
    (fun s v => sharpDegree 126525 9 (adaptiveSpanNumerator139177 s)
      (adaptiveSpanDenominator139177 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows139177)
    adaptiveSpanPrimes139177
    (fun s => sharpDegree (126525 / 2) 9 (adaptiveSpanNumerator139177 s) (adaptiveSpanDenominator139177 s))
    (fun s => sharpDegree 126525 9 (adaptiveSpanNumerator139177 s) (adaptiveSpanDenominator139177 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid139177 adaptiveOrder139177 adaptivePermutationSemantics139177
    (by rw [adaptiveSpanProfileLength139177]; decide +kernel)
    adaptiveSpanLevel139177 adaptiveSpanTreeCache139177 adaptiveSpanTreeRepresents139177
    (fun j => adaptiveSpanWitness139177.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength139177
  · exact adaptiveSpanWitnessCheck139177

/-- Every required odd cycle for a dense set, throughout 126525 ≤ n ≤ 139177. -/
theorem adaptiveSpanInterval139177 {n : ℕ} (hLn : 126525 ≤ n) (hnU : n ≤ 139177)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes139177
    adaptiveSpanNumerator139177 adaptiveSpanDenominator139177 adaptiveSpanSharpTail139177
    adaptiveSpanPrimeSupport139177 adaptiveSpanHistogram139177 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail139177
#print axioms adaptiveSpanPrimeSupport139177
#print axioms adaptiveSpanHistogram139177
#print axioms adaptiveSpanInterval139177
end Erdos883Verified
