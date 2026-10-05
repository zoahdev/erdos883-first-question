import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1840Metadata
import Erdos883AdaptiveSpan1840Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1840 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1840 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1840 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1840 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1840.length) :
    SharpTailCertificate 1840 (adaptiveSpanPrimes1840.take s)
      (adaptiveSpanNumerator1840 s) (adaptiveSpanDenominator1840 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1840 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1840 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1840 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1840 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1840 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1840 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1840 : ∀ u ∈ oddUniverse 1840,
    ∀ v ∈ oddUniverse 1840, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1840 : AdaptiveProfileRowsValid adaptiveRows1840 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1840

theorem adaptiveSpanProfileLength1840 : adaptiveRows1840.length = halfOdds 1840 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1840)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1840 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1840.length) :
    (adaptiveSpanLevel1840 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1840 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1840, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1840_0 adaptiveSpanWholeCache1840_0
  · simpa only [adaptiveSpanLevel1840, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1840_1 adaptiveSpanWholeCache1840_1
  · simpa only [adaptiveSpanLevel1840, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1840_2 adaptiveSpanWholeCache1840_2
  · simpa only [adaptiveSpanLevel1840, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1840_3 adaptiveSpanWholeCache1840_3
  · simpa only [adaptiveSpanLevel1840, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1840_4 adaptiveSpanWholeCache1840_4
  · simpa only [adaptiveSpanLevel1840, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1840_5 adaptiveSpanWholeCache1840_5

theorem adaptiveSpanTreeRepresents1840 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1840.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1840 (halfOdds 1840)
      (sharpDegree (1796 / 2) 6 (adaptiveSpanNumerator1840 s) (adaptiveSpanDenominator1840 s))
      (sharpDegree 1796 6 (adaptiveSpanNumerator1840 s) (adaptiveSpanDenominator1840 s))
      (adaptiveSpanLevel1840 s).1 (adaptiveSpanLevel1840 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1840, adaptiveSpanNumerator1840, adaptiveSpanDenominator1840, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 920) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1840 adaptiveOrder1840 adaptiveSpanNumericCheck1840_0
        adaptiveSpanEven1840_0 adaptiveSpanWhole1840_0
        adaptiveSpanEvenEntries1840_0 adaptiveSpanWholeEntries1840_0
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanEvenDomain1840_0)
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanWholeDomain1840_0)
  · simpa only [adaptiveSpanLevel1840, adaptiveSpanNumerator1840, adaptiveSpanDenominator1840, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 920) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1840 adaptiveOrder1840 adaptiveSpanNumericCheck1840_1
        adaptiveSpanEven1840_1 adaptiveSpanWhole1840_1
        adaptiveSpanEvenEntries1840_1 adaptiveSpanWholeEntries1840_1
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanEvenDomain1840_1)
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanWholeDomain1840_1)
  · simpa only [adaptiveSpanLevel1840, adaptiveSpanNumerator1840, adaptiveSpanDenominator1840, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 920) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1840 adaptiveOrder1840 adaptiveSpanNumericCheck1840_2
        adaptiveSpanEven1840_2 adaptiveSpanWhole1840_2
        adaptiveSpanEvenEntries1840_2 adaptiveSpanWholeEntries1840_2
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanEvenDomain1840_2)
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanWholeDomain1840_2)
  · simpa only [adaptiveSpanLevel1840, adaptiveSpanNumerator1840, adaptiveSpanDenominator1840, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 920) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1840 adaptiveOrder1840 adaptiveSpanNumericCheck1840_3
        adaptiveSpanEven1840_3 adaptiveSpanWhole1840_3
        adaptiveSpanEvenEntries1840_3 adaptiveSpanWholeEntries1840_3
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanEvenDomain1840_3)
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanWholeDomain1840_3)
  · simpa only [adaptiveSpanLevel1840, adaptiveSpanNumerator1840, adaptiveSpanDenominator1840, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 920) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1840 adaptiveOrder1840 adaptiveSpanNumericCheck1840_4
        adaptiveSpanEven1840_4 adaptiveSpanWhole1840_4
        adaptiveSpanEvenEntries1840_4 adaptiveSpanWholeEntries1840_4
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanEvenDomain1840_4)
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanWholeDomain1840_4)
  · simpa only [adaptiveSpanLevel1840, adaptiveSpanNumerator1840, adaptiveSpanDenominator1840, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 920) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1840 adaptiveOrder1840 adaptiveSpanNumericCheck1840_5
        adaptiveSpanEven1840_5 adaptiveSpanWhole1840_5
        adaptiveSpanEvenEntries1840_5 adaptiveSpanWholeEntries1840_5
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanEvenDomain1840_5)
        (by rw [adaptiveSpanProfileLength1840]; exact adaptiveSpanWholeDomain1840_5)

/-- The complete finite histogram certificate for 1796 ≤ n ≤ 1840. -/
theorem adaptiveSpanHistogram1840 : DegreeIntervalCertificate 1840 adaptiveSpanPrimes1840
    (fun s v => sharpDegree (1796 / 2) 6 (adaptiveSpanNumerator1840 s)
      (adaptiveSpanDenominator1840 s) (totientDensity v))
    (fun s v => sharpDegree 1796 6 (adaptiveSpanNumerator1840 s)
      (adaptiveSpanDenominator1840 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1840)
    adaptiveSpanPrimes1840
    (fun s => sharpDegree (1796 / 2) 6 (adaptiveSpanNumerator1840 s) (adaptiveSpanDenominator1840 s))
    (fun s => sharpDegree 1796 6 (adaptiveSpanNumerator1840 s) (adaptiveSpanDenominator1840 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1840 adaptiveOrder1840 (coreOrderPermutationCheck_sound adaptivePermutation1840)
    (by rw [adaptiveSpanProfileLength1840]; decide +kernel)
    adaptiveSpanLevel1840 adaptiveSpanTreeCache1840 adaptiveSpanTreeRepresents1840
    (fun j => adaptiveSpanWitness1840.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1840

/-- Every required odd cycle for a dense set, throughout 1796 ≤ n ≤ 1840. -/
theorem adaptiveSpanInterval1840 {n : ℕ} (hLn : 1796 ≤ n) (hnU : n ≤ 1840)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1840
    adaptiveSpanNumerator1840 adaptiveSpanDenominator1840 adaptiveSpanSharpTail1840
    adaptiveSpanPrimeSupport1840 adaptiveSpanHistogram1840 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1840
#print axioms adaptiveSpanPrimeSupport1840
#print axioms adaptiveSpanHistogram1840
#print axioms adaptiveSpanInterval1840
end Erdos883Verified
