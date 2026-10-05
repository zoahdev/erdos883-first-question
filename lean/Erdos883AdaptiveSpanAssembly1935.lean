import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1935Metadata
import Erdos883AdaptiveSpan1935Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1935 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1935 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1935 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1935 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1935.length) :
    SharpTailCertificate 1935 (adaptiveSpanPrimes1935.take s)
      (adaptiveSpanNumerator1935 s) (adaptiveSpanDenominator1935 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1935 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1935 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1935 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1935 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1935 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1935 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1935 : ∀ u ∈ oddUniverse 1935,
    ∀ v ∈ oddUniverse 1935, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1935 : AdaptiveProfileRowsValid adaptiveRows1935 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1935

theorem adaptiveSpanProfileLength1935 : adaptiveRows1935.length = halfOdds 1935 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1935)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1935 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1935.length) :
    (adaptiveSpanLevel1935 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1935 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1935, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1935_0 adaptiveSpanWholeCache1935_0
  · simpa only [adaptiveSpanLevel1935, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1935_1 adaptiveSpanWholeCache1935_1
  · simpa only [adaptiveSpanLevel1935, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1935_2 adaptiveSpanWholeCache1935_2
  · simpa only [adaptiveSpanLevel1935, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1935_3 adaptiveSpanWholeCache1935_3
  · simpa only [adaptiveSpanLevel1935, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1935_4 adaptiveSpanWholeCache1935_4
  · simpa only [adaptiveSpanLevel1935, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1935_5 adaptiveSpanWholeCache1935_5

theorem adaptiveSpanTreeRepresents1935 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1935.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1935 (halfOdds 1935)
      (sharpDegree (1888 / 2) 6 (adaptiveSpanNumerator1935 s) (adaptiveSpanDenominator1935 s))
      (sharpDegree 1888 6 (adaptiveSpanNumerator1935 s) (adaptiveSpanDenominator1935 s))
      (adaptiveSpanLevel1935 s).1 (adaptiveSpanLevel1935 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1935, adaptiveSpanNumerator1935, adaptiveSpanDenominator1935, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 968) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1935 adaptiveOrder1935 adaptiveSpanNumericCheck1935_0
        adaptiveSpanEven1935_0 adaptiveSpanWhole1935_0
        adaptiveSpanEvenEntries1935_0 adaptiveSpanWholeEntries1935_0
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanEvenDomain1935_0)
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanWholeDomain1935_0)
  · simpa only [adaptiveSpanLevel1935, adaptiveSpanNumerator1935, adaptiveSpanDenominator1935, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 968) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1935 adaptiveOrder1935 adaptiveSpanNumericCheck1935_1
        adaptiveSpanEven1935_1 adaptiveSpanWhole1935_1
        adaptiveSpanEvenEntries1935_1 adaptiveSpanWholeEntries1935_1
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanEvenDomain1935_1)
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanWholeDomain1935_1)
  · simpa only [adaptiveSpanLevel1935, adaptiveSpanNumerator1935, adaptiveSpanDenominator1935, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 968) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1935 adaptiveOrder1935 adaptiveSpanNumericCheck1935_2
        adaptiveSpanEven1935_2 adaptiveSpanWhole1935_2
        adaptiveSpanEvenEntries1935_2 adaptiveSpanWholeEntries1935_2
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanEvenDomain1935_2)
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanWholeDomain1935_2)
  · simpa only [adaptiveSpanLevel1935, adaptiveSpanNumerator1935, adaptiveSpanDenominator1935, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 968) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1935 adaptiveOrder1935 adaptiveSpanNumericCheck1935_3
        adaptiveSpanEven1935_3 adaptiveSpanWhole1935_3
        adaptiveSpanEvenEntries1935_3 adaptiveSpanWholeEntries1935_3
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanEvenDomain1935_3)
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanWholeDomain1935_3)
  · simpa only [adaptiveSpanLevel1935, adaptiveSpanNumerator1935, adaptiveSpanDenominator1935, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 968) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1935 adaptiveOrder1935 adaptiveSpanNumericCheck1935_4
        adaptiveSpanEven1935_4 adaptiveSpanWhole1935_4
        adaptiveSpanEvenEntries1935_4 adaptiveSpanWholeEntries1935_4
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanEvenDomain1935_4)
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanWholeDomain1935_4)
  · simpa only [adaptiveSpanLevel1935, adaptiveSpanNumerator1935, adaptiveSpanDenominator1935, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 968) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1935 adaptiveOrder1935 adaptiveSpanNumericCheck1935_5
        adaptiveSpanEven1935_5 adaptiveSpanWhole1935_5
        adaptiveSpanEvenEntries1935_5 adaptiveSpanWholeEntries1935_5
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanEvenDomain1935_5)
        (by rw [adaptiveSpanProfileLength1935]; exact adaptiveSpanWholeDomain1935_5)

/-- The complete finite histogram certificate for 1888 ≤ n ≤ 1935. -/
theorem adaptiveSpanHistogram1935 : DegreeIntervalCertificate 1935 adaptiveSpanPrimes1935
    (fun s v => sharpDegree (1888 / 2) 6 (adaptiveSpanNumerator1935 s)
      (adaptiveSpanDenominator1935 s) (totientDensity v))
    (fun s v => sharpDegree 1888 6 (adaptiveSpanNumerator1935 s)
      (adaptiveSpanDenominator1935 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1935)
    adaptiveSpanPrimes1935
    (fun s => sharpDegree (1888 / 2) 6 (adaptiveSpanNumerator1935 s) (adaptiveSpanDenominator1935 s))
    (fun s => sharpDegree 1888 6 (adaptiveSpanNumerator1935 s) (adaptiveSpanDenominator1935 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1935 adaptiveOrder1935 (coreOrderPermutationCheck_sound adaptivePermutation1935)
    (by rw [adaptiveSpanProfileLength1935]; decide +kernel)
    adaptiveSpanLevel1935 adaptiveSpanTreeCache1935 adaptiveSpanTreeRepresents1935
    (fun j => adaptiveSpanWitness1935.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1935

/-- Every required odd cycle for a dense set, throughout 1888 ≤ n ≤ 1935. -/
theorem adaptiveSpanInterval1935 {n : ℕ} (hLn : 1888 ≤ n) (hnU : n ≤ 1935)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1935
    adaptiveSpanNumerator1935 adaptiveSpanDenominator1935 adaptiveSpanSharpTail1935
    adaptiveSpanPrimeSupport1935 adaptiveSpanHistogram1935 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1935
#print axioms adaptiveSpanPrimeSupport1935
#print axioms adaptiveSpanHistogram1935
#print axioms adaptiveSpanInterval1935
end Erdos883Verified
