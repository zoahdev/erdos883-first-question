import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1887Metadata
import Erdos883AdaptiveSpan1887Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1887 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1887 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1887 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1887 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1887.length) :
    SharpTailCertificate 1887 (adaptiveSpanPrimes1887.take s)
      (adaptiveSpanNumerator1887 s) (adaptiveSpanDenominator1887 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1887 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1887 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1887 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1887 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1887 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1887 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1887 : ∀ u ∈ oddUniverse 1887,
    ∀ v ∈ oddUniverse 1887, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1887 : AdaptiveProfileRowsValid adaptiveRows1887 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1887

theorem adaptiveSpanProfileLength1887 : adaptiveRows1887.length = halfOdds 1887 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1887)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1887 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1887.length) :
    (adaptiveSpanLevel1887 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1887 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1887, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1887_0 adaptiveSpanWholeCache1887_0
  · simpa only [adaptiveSpanLevel1887, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1887_1 adaptiveSpanWholeCache1887_1
  · simpa only [adaptiveSpanLevel1887, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1887_2 adaptiveSpanWholeCache1887_2
  · simpa only [adaptiveSpanLevel1887, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1887_3 adaptiveSpanWholeCache1887_3
  · simpa only [adaptiveSpanLevel1887, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1887_4 adaptiveSpanWholeCache1887_4
  · simpa only [adaptiveSpanLevel1887, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1887_5 adaptiveSpanWholeCache1887_5

theorem adaptiveSpanTreeRepresents1887 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1887.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1887 (halfOdds 1887)
      (sharpDegree (1841 / 2) 6 (adaptiveSpanNumerator1887 s) (adaptiveSpanDenominator1887 s))
      (sharpDegree 1841 6 (adaptiveSpanNumerator1887 s) (adaptiveSpanDenominator1887 s))
      (adaptiveSpanLevel1887 s).1 (adaptiveSpanLevel1887 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1887, adaptiveSpanNumerator1887, adaptiveSpanDenominator1887, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 944) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1887 adaptiveOrder1887 adaptiveSpanNumericCheck1887_0
        adaptiveSpanEven1887_0 adaptiveSpanWhole1887_0
        adaptiveSpanEvenEntries1887_0 adaptiveSpanWholeEntries1887_0
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanEvenDomain1887_0)
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanWholeDomain1887_0)
  · simpa only [adaptiveSpanLevel1887, adaptiveSpanNumerator1887, adaptiveSpanDenominator1887, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 944) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1887 adaptiveOrder1887 adaptiveSpanNumericCheck1887_1
        adaptiveSpanEven1887_1 adaptiveSpanWhole1887_1
        adaptiveSpanEvenEntries1887_1 adaptiveSpanWholeEntries1887_1
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanEvenDomain1887_1)
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanWholeDomain1887_1)
  · simpa only [adaptiveSpanLevel1887, adaptiveSpanNumerator1887, adaptiveSpanDenominator1887, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 944) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1887 adaptiveOrder1887 adaptiveSpanNumericCheck1887_2
        adaptiveSpanEven1887_2 adaptiveSpanWhole1887_2
        adaptiveSpanEvenEntries1887_2 adaptiveSpanWholeEntries1887_2
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanEvenDomain1887_2)
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanWholeDomain1887_2)
  · simpa only [adaptiveSpanLevel1887, adaptiveSpanNumerator1887, adaptiveSpanDenominator1887, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 944) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1887 adaptiveOrder1887 adaptiveSpanNumericCheck1887_3
        adaptiveSpanEven1887_3 adaptiveSpanWhole1887_3
        adaptiveSpanEvenEntries1887_3 adaptiveSpanWholeEntries1887_3
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanEvenDomain1887_3)
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanWholeDomain1887_3)
  · simpa only [adaptiveSpanLevel1887, adaptiveSpanNumerator1887, adaptiveSpanDenominator1887, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 944) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1887 adaptiveOrder1887 adaptiveSpanNumericCheck1887_4
        adaptiveSpanEven1887_4 adaptiveSpanWhole1887_4
        adaptiveSpanEvenEntries1887_4 adaptiveSpanWholeEntries1887_4
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanEvenDomain1887_4)
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanWholeDomain1887_4)
  · simpa only [adaptiveSpanLevel1887, adaptiveSpanNumerator1887, adaptiveSpanDenominator1887, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 944) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1887 adaptiveOrder1887 adaptiveSpanNumericCheck1887_5
        adaptiveSpanEven1887_5 adaptiveSpanWhole1887_5
        adaptiveSpanEvenEntries1887_5 adaptiveSpanWholeEntries1887_5
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanEvenDomain1887_5)
        (by rw [adaptiveSpanProfileLength1887]; exact adaptiveSpanWholeDomain1887_5)

/-- The complete finite histogram certificate for 1841 ≤ n ≤ 1887. -/
theorem adaptiveSpanHistogram1887 : DegreeIntervalCertificate 1887 adaptiveSpanPrimes1887
    (fun s v => sharpDegree (1841 / 2) 6 (adaptiveSpanNumerator1887 s)
      (adaptiveSpanDenominator1887 s) (totientDensity v))
    (fun s v => sharpDegree 1841 6 (adaptiveSpanNumerator1887 s)
      (adaptiveSpanDenominator1887 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1887)
    adaptiveSpanPrimes1887
    (fun s => sharpDegree (1841 / 2) 6 (adaptiveSpanNumerator1887 s) (adaptiveSpanDenominator1887 s))
    (fun s => sharpDegree 1841 6 (adaptiveSpanNumerator1887 s) (adaptiveSpanDenominator1887 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1887 adaptiveOrder1887 (coreOrderPermutationCheck_sound adaptivePermutation1887)
    (by rw [adaptiveSpanProfileLength1887]; decide +kernel)
    adaptiveSpanLevel1887 adaptiveSpanTreeCache1887 adaptiveSpanTreeRepresents1887
    (fun j => adaptiveSpanWitness1887.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1887

/-- Every required odd cycle for a dense set, throughout 1841 ≤ n ≤ 1887. -/
theorem adaptiveSpanInterval1887 {n : ℕ} (hLn : 1841 ≤ n) (hnU : n ≤ 1887)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1887
    adaptiveSpanNumerator1887 adaptiveSpanDenominator1887 adaptiveSpanSharpTail1887
    adaptiveSpanPrimeSupport1887 adaptiveSpanHistogram1887 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1887
#print axioms adaptiveSpanPrimeSupport1887
#print axioms adaptiveSpanHistogram1887
#print axioms adaptiveSpanInterval1887
end Erdos883Verified
