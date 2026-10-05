import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1751Metadata
import Erdos883AdaptiveSpan1751Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1751 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1751 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1751 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1751 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1751.length) :
    SharpTailCertificate 1751 (adaptiveSpanPrimes1751.take s)
      (adaptiveSpanNumerator1751 s) (adaptiveSpanDenominator1751 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1751 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1751 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1751 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1751 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1751 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1751 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1751 : ∀ u ∈ oddUniverse 1751,
    ∀ v ∈ oddUniverse 1751, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1751 : AdaptiveProfileRowsValid adaptiveRows1751 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1751

theorem adaptiveSpanProfileLength1751 : adaptiveRows1751.length = halfOdds 1751 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1751)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1751 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1751.length) :
    (adaptiveSpanLevel1751 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1751 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1751, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1751_0 adaptiveSpanWholeCache1751_0
  · simpa only [adaptiveSpanLevel1751, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1751_1 adaptiveSpanWholeCache1751_1
  · simpa only [adaptiveSpanLevel1751, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1751_2 adaptiveSpanWholeCache1751_2
  · simpa only [adaptiveSpanLevel1751, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1751_3 adaptiveSpanWholeCache1751_3
  · simpa only [adaptiveSpanLevel1751, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1751_4 adaptiveSpanWholeCache1751_4
  · simpa only [adaptiveSpanLevel1751, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1751_5 adaptiveSpanWholeCache1751_5

theorem adaptiveSpanTreeRepresents1751 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1751.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1751 (halfOdds 1751)
      (sharpDegree (1709 / 2) 6 (adaptiveSpanNumerator1751 s) (adaptiveSpanDenominator1751 s))
      (sharpDegree 1709 6 (adaptiveSpanNumerator1751 s) (adaptiveSpanDenominator1751 s))
      (adaptiveSpanLevel1751 s).1 (adaptiveSpanLevel1751 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1751, adaptiveSpanNumerator1751, adaptiveSpanDenominator1751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 876) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1751 adaptiveOrder1751 adaptiveSpanNumericCheck1751_0
        adaptiveSpanEven1751_0 adaptiveSpanWhole1751_0
        adaptiveSpanEvenEntries1751_0 adaptiveSpanWholeEntries1751_0
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanEvenDomain1751_0)
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanWholeDomain1751_0)
  · simpa only [adaptiveSpanLevel1751, adaptiveSpanNumerator1751, adaptiveSpanDenominator1751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 876) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1751 adaptiveOrder1751 adaptiveSpanNumericCheck1751_1
        adaptiveSpanEven1751_1 adaptiveSpanWhole1751_1
        adaptiveSpanEvenEntries1751_1 adaptiveSpanWholeEntries1751_1
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanEvenDomain1751_1)
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanWholeDomain1751_1)
  · simpa only [adaptiveSpanLevel1751, adaptiveSpanNumerator1751, adaptiveSpanDenominator1751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 876) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1751 adaptiveOrder1751 adaptiveSpanNumericCheck1751_2
        adaptiveSpanEven1751_2 adaptiveSpanWhole1751_2
        adaptiveSpanEvenEntries1751_2 adaptiveSpanWholeEntries1751_2
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanEvenDomain1751_2)
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanWholeDomain1751_2)
  · simpa only [adaptiveSpanLevel1751, adaptiveSpanNumerator1751, adaptiveSpanDenominator1751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 876) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1751 adaptiveOrder1751 adaptiveSpanNumericCheck1751_3
        adaptiveSpanEven1751_3 adaptiveSpanWhole1751_3
        adaptiveSpanEvenEntries1751_3 adaptiveSpanWholeEntries1751_3
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanEvenDomain1751_3)
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanWholeDomain1751_3)
  · simpa only [adaptiveSpanLevel1751, adaptiveSpanNumerator1751, adaptiveSpanDenominator1751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 876) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1751 adaptiveOrder1751 adaptiveSpanNumericCheck1751_4
        adaptiveSpanEven1751_4 adaptiveSpanWhole1751_4
        adaptiveSpanEvenEntries1751_4 adaptiveSpanWholeEntries1751_4
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanEvenDomain1751_4)
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanWholeDomain1751_4)
  · simpa only [adaptiveSpanLevel1751, adaptiveSpanNumerator1751, adaptiveSpanDenominator1751, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 876) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1751 adaptiveOrder1751 adaptiveSpanNumericCheck1751_5
        adaptiveSpanEven1751_5 adaptiveSpanWhole1751_5
        adaptiveSpanEvenEntries1751_5 adaptiveSpanWholeEntries1751_5
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanEvenDomain1751_5)
        (by rw [adaptiveSpanProfileLength1751]; exact adaptiveSpanWholeDomain1751_5)

/-- The complete finite histogram certificate for 1709 ≤ n ≤ 1751. -/
theorem adaptiveSpanHistogram1751 : DegreeIntervalCertificate 1751 adaptiveSpanPrimes1751
    (fun s v => sharpDegree (1709 / 2) 6 (adaptiveSpanNumerator1751 s)
      (adaptiveSpanDenominator1751 s) (totientDensity v))
    (fun s v => sharpDegree 1709 6 (adaptiveSpanNumerator1751 s)
      (adaptiveSpanDenominator1751 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1751)
    adaptiveSpanPrimes1751
    (fun s => sharpDegree (1709 / 2) 6 (adaptiveSpanNumerator1751 s) (adaptiveSpanDenominator1751 s))
    (fun s => sharpDegree 1709 6 (adaptiveSpanNumerator1751 s) (adaptiveSpanDenominator1751 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1751 adaptiveOrder1751 (coreOrderPermutationCheck_sound adaptivePermutation1751)
    (by rw [adaptiveSpanProfileLength1751]; decide +kernel)
    adaptiveSpanLevel1751 adaptiveSpanTreeCache1751 adaptiveSpanTreeRepresents1751
    (fun j => adaptiveSpanWitness1751.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1751

/-- Every required odd cycle for a dense set, throughout 1709 ≤ n ≤ 1751. -/
theorem adaptiveSpanInterval1751 {n : ℕ} (hLn : 1709 ≤ n) (hnU : n ≤ 1751)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1751
    adaptiveSpanNumerator1751 adaptiveSpanDenominator1751 adaptiveSpanSharpTail1751
    adaptiveSpanPrimeSupport1751 adaptiveSpanHistogram1751 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1751
#print axioms adaptiveSpanPrimeSupport1751
#print axioms adaptiveSpanHistogram1751
#print axioms adaptiveSpanInterval1751
end Erdos883Verified
