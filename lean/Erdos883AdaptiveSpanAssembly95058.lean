import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate95058Metadata
import Erdos883AdaptiveSpan95058Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate95058PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes95058 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator95058 : ℕ → ℕ
  | 0 => 5760
  | 1 => 46080
  | 2 => 11520
  | 3 => 34560
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator95058 : ℕ → ℕ
  | 0 => 15015
  | 1 => 85085
  | 2 => 17017
  | 3 => 46189
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail95058 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes95058.length) :
    SharpTailCertificate 95058 (adaptiveSpanPrimes95058.take s)
      (adaptiveSpanNumerator95058 s) (adaptiveSpanDenominator95058 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 95058 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 95058 [3] 46080 85085
    refine ⟨by decide, {5, 7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 95058 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 95058 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 95058 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 95058 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 95058 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 95058 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 95058 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport95058 : ∀ u ∈ oddUniverse 95058,
    ∀ v ∈ oddUniverse 95058, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid95058 : AdaptiveProfileRowsValid adaptiveRows95058 :=
  coreProfileMetadataCheck_sound adaptiveMetadata95058

theorem adaptiveSpanProfileLength95058 : adaptiveRows95058.length = halfOdds 95058 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics95058
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache95058 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes95058.length) :
    (adaptiveSpanLevel95058 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel95058 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel95058, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache95058_0 adaptiveSpanWholeCache95058_0
  · simpa only [adaptiveSpanLevel95058, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache95058_1 adaptiveSpanWholeCache95058_1
  · simpa only [adaptiveSpanLevel95058, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache95058_2 adaptiveSpanWholeCache95058_2
  · simpa only [adaptiveSpanLevel95058, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache95058_3 adaptiveSpanWholeCache95058_3
  · simpa only [adaptiveSpanLevel95058, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache95058_4 adaptiveSpanWholeCache95058_4
  · simpa only [adaptiveSpanLevel95058, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache95058_5 adaptiveSpanWholeCache95058_5
  · simpa only [adaptiveSpanLevel95058, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache95058_6 adaptiveSpanWholeCache95058_6
  · simpa only [adaptiveSpanLevel95058, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache95058_7 adaptiveSpanWholeCache95058_7
  · simpa only [adaptiveSpanLevel95058, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache95058_8 adaptiveSpanWholeCache95058_8

theorem adaptiveSpanTreeRepresents95058 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes95058.length) :
    AdaptiveSpanTreeRepresents adaptiveRows95058 (halfOdds 95058)
      (sharpDegree (86417 / 2) 9 (adaptiveSpanNumerator95058 s) (adaptiveSpanDenominator95058 s))
      (sharpDegree 86417 9 (adaptiveSpanNumerator95058 s) (adaptiveSpanDenominator95058 s))
      (adaptiveSpanLevel95058 s).1 (adaptiveSpanLevel95058 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel95058, adaptiveSpanNumerator95058, adaptiveSpanDenominator95058, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 47529) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid95058 adaptiveOrder95058 adaptiveSpanNumericCheck95058_0
        adaptiveSpanEven95058_0 adaptiveSpanWhole95058_0
        adaptiveSpanEvenEntries95058_0 adaptiveSpanWholeEntries95058_0
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanEvenDomain95058_0)
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanWholeDomain95058_0)
  · simpa only [adaptiveSpanLevel95058, adaptiveSpanNumerator95058, adaptiveSpanDenominator95058, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 47529) (by decide : 0 < 85085)
        adaptiveSpanProfilesValid95058 adaptiveOrder95058 adaptiveSpanNumericCheck95058_1
        adaptiveSpanEven95058_1 adaptiveSpanWhole95058_1
        adaptiveSpanEvenEntries95058_1 adaptiveSpanWholeEntries95058_1
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanEvenDomain95058_1)
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanWholeDomain95058_1)
  · simpa only [adaptiveSpanLevel95058, adaptiveSpanNumerator95058, adaptiveSpanDenominator95058, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 47529) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid95058 adaptiveOrder95058 adaptiveSpanNumericCheck95058_2
        adaptiveSpanEven95058_2 adaptiveSpanWhole95058_2
        adaptiveSpanEvenEntries95058_2 adaptiveSpanWholeEntries95058_2
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanEvenDomain95058_2)
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanWholeDomain95058_2)
  · simpa only [adaptiveSpanLevel95058, adaptiveSpanNumerator95058, adaptiveSpanDenominator95058, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 47529) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid95058 adaptiveOrder95058 adaptiveSpanNumericCheck95058_3
        adaptiveSpanEven95058_3 adaptiveSpanWhole95058_3
        adaptiveSpanEvenEntries95058_3 adaptiveSpanWholeEntries95058_3
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanEvenDomain95058_3)
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanWholeDomain95058_3)
  · simpa only [adaptiveSpanLevel95058, adaptiveSpanNumerator95058, adaptiveSpanDenominator95058, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 47529) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid95058 adaptiveOrder95058 adaptiveSpanNumericCheck95058_4
        adaptiveSpanEven95058_4 adaptiveSpanWhole95058_4
        adaptiveSpanEvenEntries95058_4 adaptiveSpanWholeEntries95058_4
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanEvenDomain95058_4)
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanWholeDomain95058_4)
  · simpa only [adaptiveSpanLevel95058, adaptiveSpanNumerator95058, adaptiveSpanDenominator95058, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 47529) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid95058 adaptiveOrder95058 adaptiveSpanNumericCheck95058_5
        adaptiveSpanEven95058_5 adaptiveSpanWhole95058_5
        adaptiveSpanEvenEntries95058_5 adaptiveSpanWholeEntries95058_5
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanEvenDomain95058_5)
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanWholeDomain95058_5)
  · simpa only [adaptiveSpanLevel95058, adaptiveSpanNumerator95058, adaptiveSpanDenominator95058, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 47529) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid95058 adaptiveOrder95058 adaptiveSpanNumericCheck95058_6
        adaptiveSpanEven95058_6 adaptiveSpanWhole95058_6
        adaptiveSpanEvenEntries95058_6 adaptiveSpanWholeEntries95058_6
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanEvenDomain95058_6)
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanWholeDomain95058_6)
  · simpa only [adaptiveSpanLevel95058, adaptiveSpanNumerator95058, adaptiveSpanDenominator95058, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 47529) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid95058 adaptiveOrder95058 adaptiveSpanNumericCheck95058_7
        adaptiveSpanEven95058_7 adaptiveSpanWhole95058_7
        adaptiveSpanEvenEntries95058_7 adaptiveSpanWholeEntries95058_7
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanEvenDomain95058_7)
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanWholeDomain95058_7)
  · simpa only [adaptiveSpanLevel95058, adaptiveSpanNumerator95058, adaptiveSpanDenominator95058, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 47529) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid95058 adaptiveOrder95058 adaptiveSpanNumericCheck95058_8
        adaptiveSpanEven95058_8 adaptiveSpanWhole95058_8
        adaptiveSpanEvenEntries95058_8 adaptiveSpanWholeEntries95058_8
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanEvenDomain95058_8)
        (by rw [adaptiveSpanProfileLength95058]; exact adaptiveSpanWholeDomain95058_8)

/-- The complete finite histogram certificate for 86417 ≤ n ≤ 95058. -/
theorem adaptiveSpanHistogram95058 : DegreeIntervalCertificate 95058 adaptiveSpanPrimes95058
    (fun s v => sharpDegree (86417 / 2) 9 (adaptiveSpanNumerator95058 s)
      (adaptiveSpanDenominator95058 s) (totientDensity v))
    (fun s v => sharpDegree 86417 9 (adaptiveSpanNumerator95058 s)
      (adaptiveSpanDenominator95058 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows95058)
    adaptiveSpanPrimes95058
    (fun s => sharpDegree (86417 / 2) 9 (adaptiveSpanNumerator95058 s) (adaptiveSpanDenominator95058 s))
    (fun s => sharpDegree 86417 9 (adaptiveSpanNumerator95058 s) (adaptiveSpanDenominator95058 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid95058 adaptiveOrder95058 adaptivePermutationSemantics95058
    (by rw [adaptiveSpanProfileLength95058]; decide +kernel)
    adaptiveSpanLevel95058 adaptiveSpanTreeCache95058 adaptiveSpanTreeRepresents95058
    (fun j => adaptiveSpanWitness95058.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength95058
  · exact adaptiveSpanWitnessCheck95058

/-- Every required odd cycle for a dense set, throughout 86417 ≤ n ≤ 95058. -/
theorem adaptiveSpanInterval95058 {n : ℕ} (hLn : 86417 ≤ n) (hnU : n ≤ 95058)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes95058
    adaptiveSpanNumerator95058 adaptiveSpanDenominator95058 adaptiveSpanSharpTail95058
    adaptiveSpanPrimeSupport95058 adaptiveSpanHistogram95058 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail95058
#print axioms adaptiveSpanPrimeSupport95058
#print axioms adaptiveSpanHistogram95058
#print axioms adaptiveSpanInterval95058
end Erdos883Verified
