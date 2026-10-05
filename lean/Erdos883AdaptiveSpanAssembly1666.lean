import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1666Metadata
import Erdos883AdaptiveSpan1666Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1666 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1666 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1666 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1666 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1666.length) :
    SharpTailCertificate 1666 (adaptiveSpanPrimes1666.take s)
      (adaptiveSpanNumerator1666 s) (adaptiveSpanDenominator1666 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1666 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1666 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1666 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1666 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1666 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1666 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1666 : ∀ u ∈ oddUniverse 1666,
    ∀ v ∈ oddUniverse 1666, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1666 : AdaptiveProfileRowsValid adaptiveRows1666 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1666

theorem adaptiveSpanProfileLength1666 : adaptiveRows1666.length = halfOdds 1666 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1666)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1666 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1666.length) :
    (adaptiveSpanLevel1666 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1666 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1666, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1666_0 adaptiveSpanWholeCache1666_0
  · simpa only [adaptiveSpanLevel1666, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1666_1 adaptiveSpanWholeCache1666_1
  · simpa only [adaptiveSpanLevel1666, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1666_2 adaptiveSpanWholeCache1666_2
  · simpa only [adaptiveSpanLevel1666, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1666_3 adaptiveSpanWholeCache1666_3
  · simpa only [adaptiveSpanLevel1666, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1666_4 adaptiveSpanWholeCache1666_4
  · simpa only [adaptiveSpanLevel1666, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1666_5 adaptiveSpanWholeCache1666_5

theorem adaptiveSpanTreeRepresents1666 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1666.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1666 (halfOdds 1666)
      (sharpDegree (1626 / 2) 6 (adaptiveSpanNumerator1666 s) (adaptiveSpanDenominator1666 s))
      (sharpDegree 1626 6 (adaptiveSpanNumerator1666 s) (adaptiveSpanDenominator1666 s))
      (adaptiveSpanLevel1666 s).1 (adaptiveSpanLevel1666 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1666, adaptiveSpanNumerator1666, adaptiveSpanDenominator1666, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 833) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1666 adaptiveOrder1666 adaptiveSpanNumericCheck1666_0
        adaptiveSpanEven1666_0 adaptiveSpanWhole1666_0
        adaptiveSpanEvenEntries1666_0 adaptiveSpanWholeEntries1666_0
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanEvenDomain1666_0)
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanWholeDomain1666_0)
  · simpa only [adaptiveSpanLevel1666, adaptiveSpanNumerator1666, adaptiveSpanDenominator1666, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 833) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1666 adaptiveOrder1666 adaptiveSpanNumericCheck1666_1
        adaptiveSpanEven1666_1 adaptiveSpanWhole1666_1
        adaptiveSpanEvenEntries1666_1 adaptiveSpanWholeEntries1666_1
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanEvenDomain1666_1)
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanWholeDomain1666_1)
  · simpa only [adaptiveSpanLevel1666, adaptiveSpanNumerator1666, adaptiveSpanDenominator1666, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 833) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1666 adaptiveOrder1666 adaptiveSpanNumericCheck1666_2
        adaptiveSpanEven1666_2 adaptiveSpanWhole1666_2
        adaptiveSpanEvenEntries1666_2 adaptiveSpanWholeEntries1666_2
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanEvenDomain1666_2)
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanWholeDomain1666_2)
  · simpa only [adaptiveSpanLevel1666, adaptiveSpanNumerator1666, adaptiveSpanDenominator1666, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 833) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1666 adaptiveOrder1666 adaptiveSpanNumericCheck1666_3
        adaptiveSpanEven1666_3 adaptiveSpanWhole1666_3
        adaptiveSpanEvenEntries1666_3 adaptiveSpanWholeEntries1666_3
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanEvenDomain1666_3)
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanWholeDomain1666_3)
  · simpa only [adaptiveSpanLevel1666, adaptiveSpanNumerator1666, adaptiveSpanDenominator1666, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 833) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1666 adaptiveOrder1666 adaptiveSpanNumericCheck1666_4
        adaptiveSpanEven1666_4 adaptiveSpanWhole1666_4
        adaptiveSpanEvenEntries1666_4 adaptiveSpanWholeEntries1666_4
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanEvenDomain1666_4)
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanWholeDomain1666_4)
  · simpa only [adaptiveSpanLevel1666, adaptiveSpanNumerator1666, adaptiveSpanDenominator1666, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 833) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1666 adaptiveOrder1666 adaptiveSpanNumericCheck1666_5
        adaptiveSpanEven1666_5 adaptiveSpanWhole1666_5
        adaptiveSpanEvenEntries1666_5 adaptiveSpanWholeEntries1666_5
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanEvenDomain1666_5)
        (by rw [adaptiveSpanProfileLength1666]; exact adaptiveSpanWholeDomain1666_5)

/-- The complete finite histogram certificate for 1626 ≤ n ≤ 1666. -/
theorem adaptiveSpanHistogram1666 : DegreeIntervalCertificate 1666 adaptiveSpanPrimes1666
    (fun s v => sharpDegree (1626 / 2) 6 (adaptiveSpanNumerator1666 s)
      (adaptiveSpanDenominator1666 s) (totientDensity v))
    (fun s v => sharpDegree 1626 6 (adaptiveSpanNumerator1666 s)
      (adaptiveSpanDenominator1666 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1666)
    adaptiveSpanPrimes1666
    (fun s => sharpDegree (1626 / 2) 6 (adaptiveSpanNumerator1666 s) (adaptiveSpanDenominator1666 s))
    (fun s => sharpDegree 1626 6 (adaptiveSpanNumerator1666 s) (adaptiveSpanDenominator1666 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1666 adaptiveOrder1666 (coreOrderPermutationCheck_sound adaptivePermutation1666)
    (by rw [adaptiveSpanProfileLength1666]; decide +kernel)
    adaptiveSpanLevel1666 adaptiveSpanTreeCache1666 adaptiveSpanTreeRepresents1666
    (fun j => adaptiveSpanWitness1666.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1666

/-- Every required odd cycle for a dense set, throughout 1626 ≤ n ≤ 1666. -/
theorem adaptiveSpanInterval1666 {n : ℕ} (hLn : 1626 ≤ n) (hnU : n ≤ 1666)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1666
    adaptiveSpanNumerator1666 adaptiveSpanDenominator1666 adaptiveSpanSharpTail1666
    adaptiveSpanPrimeSupport1666 adaptiveSpanHistogram1666 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1666
#print axioms adaptiveSpanPrimeSupport1666
#print axioms adaptiveSpanHistogram1666
#print axioms adaptiveSpanInterval1666
end Erdos883Verified
