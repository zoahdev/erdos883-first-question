import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1984Metadata
import Erdos883AdaptiveSpan1984Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1984 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1984 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1984 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1984 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1984.length) :
    SharpTailCertificate 1984 (adaptiveSpanPrimes1984.take s)
      (adaptiveSpanNumerator1984 s) (adaptiveSpanDenominator1984 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1984 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1984 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1984 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1984 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1984 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1984 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1984 : ∀ u ∈ oddUniverse 1984,
    ∀ v ∈ oddUniverse 1984, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1984 : AdaptiveProfileRowsValid adaptiveRows1984 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1984

theorem adaptiveSpanProfileLength1984 : adaptiveRows1984.length = halfOdds 1984 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1984)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1984 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1984.length) :
    (adaptiveSpanLevel1984 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1984 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1984, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1984_0 adaptiveSpanWholeCache1984_0
  · simpa only [adaptiveSpanLevel1984, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1984_1 adaptiveSpanWholeCache1984_1
  · simpa only [adaptiveSpanLevel1984, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1984_2 adaptiveSpanWholeCache1984_2
  · simpa only [adaptiveSpanLevel1984, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1984_3 adaptiveSpanWholeCache1984_3
  · simpa only [adaptiveSpanLevel1984, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1984_4 adaptiveSpanWholeCache1984_4
  · simpa only [adaptiveSpanLevel1984, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1984_5 adaptiveSpanWholeCache1984_5

theorem adaptiveSpanTreeRepresents1984 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1984.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1984 (halfOdds 1984)
      (sharpDegree (1936 / 2) 6 (adaptiveSpanNumerator1984 s) (adaptiveSpanDenominator1984 s))
      (sharpDegree 1936 6 (adaptiveSpanNumerator1984 s) (adaptiveSpanDenominator1984 s))
      (adaptiveSpanLevel1984 s).1 (adaptiveSpanLevel1984 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1984, adaptiveSpanNumerator1984, adaptiveSpanDenominator1984, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 992) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1984 adaptiveOrder1984 adaptiveSpanNumericCheck1984_0
        adaptiveSpanEven1984_0 adaptiveSpanWhole1984_0
        adaptiveSpanEvenEntries1984_0 adaptiveSpanWholeEntries1984_0
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanEvenDomain1984_0)
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanWholeDomain1984_0)
  · simpa only [adaptiveSpanLevel1984, adaptiveSpanNumerator1984, adaptiveSpanDenominator1984, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 992) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1984 adaptiveOrder1984 adaptiveSpanNumericCheck1984_1
        adaptiveSpanEven1984_1 adaptiveSpanWhole1984_1
        adaptiveSpanEvenEntries1984_1 adaptiveSpanWholeEntries1984_1
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanEvenDomain1984_1)
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanWholeDomain1984_1)
  · simpa only [adaptiveSpanLevel1984, adaptiveSpanNumerator1984, adaptiveSpanDenominator1984, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 992) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1984 adaptiveOrder1984 adaptiveSpanNumericCheck1984_2
        adaptiveSpanEven1984_2 adaptiveSpanWhole1984_2
        adaptiveSpanEvenEntries1984_2 adaptiveSpanWholeEntries1984_2
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanEvenDomain1984_2)
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanWholeDomain1984_2)
  · simpa only [adaptiveSpanLevel1984, adaptiveSpanNumerator1984, adaptiveSpanDenominator1984, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 992) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1984 adaptiveOrder1984 adaptiveSpanNumericCheck1984_3
        adaptiveSpanEven1984_3 adaptiveSpanWhole1984_3
        adaptiveSpanEvenEntries1984_3 adaptiveSpanWholeEntries1984_3
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanEvenDomain1984_3)
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanWholeDomain1984_3)
  · simpa only [adaptiveSpanLevel1984, adaptiveSpanNumerator1984, adaptiveSpanDenominator1984, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 992) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1984 adaptiveOrder1984 adaptiveSpanNumericCheck1984_4
        adaptiveSpanEven1984_4 adaptiveSpanWhole1984_4
        adaptiveSpanEvenEntries1984_4 adaptiveSpanWholeEntries1984_4
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanEvenDomain1984_4)
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanWholeDomain1984_4)
  · simpa only [adaptiveSpanLevel1984, adaptiveSpanNumerator1984, adaptiveSpanDenominator1984, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 992) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1984 adaptiveOrder1984 adaptiveSpanNumericCheck1984_5
        adaptiveSpanEven1984_5 adaptiveSpanWhole1984_5
        adaptiveSpanEvenEntries1984_5 adaptiveSpanWholeEntries1984_5
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanEvenDomain1984_5)
        (by rw [adaptiveSpanProfileLength1984]; exact adaptiveSpanWholeDomain1984_5)

/-- The complete finite histogram certificate for 1936 ≤ n ≤ 1984. -/
theorem adaptiveSpanHistogram1984 : DegreeIntervalCertificate 1984 adaptiveSpanPrimes1984
    (fun s v => sharpDegree (1936 / 2) 6 (adaptiveSpanNumerator1984 s)
      (adaptiveSpanDenominator1984 s) (totientDensity v))
    (fun s v => sharpDegree 1936 6 (adaptiveSpanNumerator1984 s)
      (adaptiveSpanDenominator1984 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1984)
    adaptiveSpanPrimes1984
    (fun s => sharpDegree (1936 / 2) 6 (adaptiveSpanNumerator1984 s) (adaptiveSpanDenominator1984 s))
    (fun s => sharpDegree 1936 6 (adaptiveSpanNumerator1984 s) (adaptiveSpanDenominator1984 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1984 adaptiveOrder1984 (coreOrderPermutationCheck_sound adaptivePermutation1984)
    (by rw [adaptiveSpanProfileLength1984]; decide +kernel)
    adaptiveSpanLevel1984 adaptiveSpanTreeCache1984 adaptiveSpanTreeRepresents1984
    (fun j => adaptiveSpanWitness1984.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1984

/-- Every required odd cycle for a dense set, throughout 1936 ≤ n ≤ 1984. -/
theorem adaptiveSpanInterval1984 {n : ℕ} (hLn : 1936 ≤ n) (hnU : n ≤ 1984)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1984
    adaptiveSpanNumerator1984 adaptiveSpanDenominator1984 adaptiveSpanSharpTail1984
    adaptiveSpanPrimeSupport1984 adaptiveSpanHistogram1984 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1984
#print axioms adaptiveSpanPrimeSupport1984
#print axioms adaptiveSpanHistogram1984
#print axioms adaptiveSpanInterval1984
end Erdos883Verified
