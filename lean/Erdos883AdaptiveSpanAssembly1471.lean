import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1471Metadata
import Erdos883AdaptiveSpan1471Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1471 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1471 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1471 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1471 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1471.length) :
    SharpTailCertificate 1471 (adaptiveSpanPrimes1471.take s)
      (adaptiveSpanNumerator1471 s) (adaptiveSpanDenominator1471 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1471 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1471 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1471 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1471 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1471 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1471 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1471 : ∀ u ∈ oddUniverse 1471,
    ∀ v ∈ oddUniverse 1471, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1471 : AdaptiveProfileRowsValid adaptiveRows1471 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1471

theorem adaptiveSpanProfileLength1471 : adaptiveRows1471.length = halfOdds 1471 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1471)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1471 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1471.length) :
    (adaptiveSpanLevel1471 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1471 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1471, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1471_0 adaptiveSpanWholeCache1471_0
  · simpa only [adaptiveSpanLevel1471, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1471_1 adaptiveSpanWholeCache1471_1
  · simpa only [adaptiveSpanLevel1471, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1471_2 adaptiveSpanWholeCache1471_2
  · simpa only [adaptiveSpanLevel1471, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1471_3 adaptiveSpanWholeCache1471_3
  · simpa only [adaptiveSpanLevel1471, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1471_4 adaptiveSpanWholeCache1471_4
  · simpa only [adaptiveSpanLevel1471, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1471_5 adaptiveSpanWholeCache1471_5

theorem adaptiveSpanTreeRepresents1471 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1471.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1471 (halfOdds 1471)
      (sharpDegree (1436 / 2) 6 (adaptiveSpanNumerator1471 s) (adaptiveSpanDenominator1471 s))
      (sharpDegree 1436 6 (adaptiveSpanNumerator1471 s) (adaptiveSpanDenominator1471 s))
      (adaptiveSpanLevel1471 s).1 (adaptiveSpanLevel1471 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1471, adaptiveSpanNumerator1471, adaptiveSpanDenominator1471, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 736) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1471 adaptiveOrder1471 adaptiveSpanNumericCheck1471_0
        adaptiveSpanEven1471_0 adaptiveSpanWhole1471_0
        adaptiveSpanEvenEntries1471_0 adaptiveSpanWholeEntries1471_0
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanEvenDomain1471_0)
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanWholeDomain1471_0)
  · simpa only [adaptiveSpanLevel1471, adaptiveSpanNumerator1471, adaptiveSpanDenominator1471, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 736) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1471 adaptiveOrder1471 adaptiveSpanNumericCheck1471_1
        adaptiveSpanEven1471_1 adaptiveSpanWhole1471_1
        adaptiveSpanEvenEntries1471_1 adaptiveSpanWholeEntries1471_1
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanEvenDomain1471_1)
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanWholeDomain1471_1)
  · simpa only [adaptiveSpanLevel1471, adaptiveSpanNumerator1471, adaptiveSpanDenominator1471, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 736) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1471 adaptiveOrder1471 adaptiveSpanNumericCheck1471_2
        adaptiveSpanEven1471_2 adaptiveSpanWhole1471_2
        adaptiveSpanEvenEntries1471_2 adaptiveSpanWholeEntries1471_2
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanEvenDomain1471_2)
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanWholeDomain1471_2)
  · simpa only [adaptiveSpanLevel1471, adaptiveSpanNumerator1471, adaptiveSpanDenominator1471, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 736) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1471 adaptiveOrder1471 adaptiveSpanNumericCheck1471_3
        adaptiveSpanEven1471_3 adaptiveSpanWhole1471_3
        adaptiveSpanEvenEntries1471_3 adaptiveSpanWholeEntries1471_3
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanEvenDomain1471_3)
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanWholeDomain1471_3)
  · simpa only [adaptiveSpanLevel1471, adaptiveSpanNumerator1471, adaptiveSpanDenominator1471, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 736) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1471 adaptiveOrder1471 adaptiveSpanNumericCheck1471_4
        adaptiveSpanEven1471_4 adaptiveSpanWhole1471_4
        adaptiveSpanEvenEntries1471_4 adaptiveSpanWholeEntries1471_4
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanEvenDomain1471_4)
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanWholeDomain1471_4)
  · simpa only [adaptiveSpanLevel1471, adaptiveSpanNumerator1471, adaptiveSpanDenominator1471, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 736) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1471 adaptiveOrder1471 adaptiveSpanNumericCheck1471_5
        adaptiveSpanEven1471_5 adaptiveSpanWhole1471_5
        adaptiveSpanEvenEntries1471_5 adaptiveSpanWholeEntries1471_5
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanEvenDomain1471_5)
        (by rw [adaptiveSpanProfileLength1471]; exact adaptiveSpanWholeDomain1471_5)

/-- The complete finite histogram certificate for 1436 ≤ n ≤ 1471. -/
theorem adaptiveSpanHistogram1471 : DegreeIntervalCertificate 1471 adaptiveSpanPrimes1471
    (fun s v => sharpDegree (1436 / 2) 6 (adaptiveSpanNumerator1471 s)
      (adaptiveSpanDenominator1471 s) (totientDensity v))
    (fun s v => sharpDegree 1436 6 (adaptiveSpanNumerator1471 s)
      (adaptiveSpanDenominator1471 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1471)
    adaptiveSpanPrimes1471
    (fun s => sharpDegree (1436 / 2) 6 (adaptiveSpanNumerator1471 s) (adaptiveSpanDenominator1471 s))
    (fun s => sharpDegree 1436 6 (adaptiveSpanNumerator1471 s) (adaptiveSpanDenominator1471 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1471 adaptiveOrder1471 (coreOrderPermutationCheck_sound adaptivePermutation1471)
    (by rw [adaptiveSpanProfileLength1471]; decide +kernel)
    adaptiveSpanLevel1471 adaptiveSpanTreeCache1471 adaptiveSpanTreeRepresents1471
    (fun j => adaptiveSpanWitness1471.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1471

/-- Every required odd cycle for a dense set, throughout 1436 ≤ n ≤ 1471. -/
theorem adaptiveSpanInterval1471 {n : ℕ} (hLn : 1436 ≤ n) (hnU : n ≤ 1471)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1471
    adaptiveSpanNumerator1471 adaptiveSpanDenominator1471 adaptiveSpanSharpTail1471
    adaptiveSpanPrimeSupport1471 adaptiveSpanHistogram1471 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1471
#print axioms adaptiveSpanPrimeSupport1471
#print axioms adaptiveSpanHistogram1471
#print axioms adaptiveSpanInterval1471
end Erdos883Verified
