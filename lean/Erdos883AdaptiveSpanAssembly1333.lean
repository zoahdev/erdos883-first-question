import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1333Metadata
import Erdos883AdaptiveSpan1333Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1333 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1333 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1333 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1333 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1333.length) :
    SharpTailCertificate 1333 (adaptiveSpanPrimes1333.take s)
      (adaptiveSpanNumerator1333 s) (adaptiveSpanDenominator1333 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1333 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1333 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1333 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1333 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1333 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1333 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1333 : ∀ u ∈ oddUniverse 1333,
    ∀ v ∈ oddUniverse 1333, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1333 : AdaptiveProfileRowsValid adaptiveRows1333 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1333

theorem adaptiveSpanProfileLength1333 : adaptiveRows1333.length = halfOdds 1333 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1333)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1333 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1333.length) :
    (adaptiveSpanLevel1333 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1333 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1333, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1333_0 adaptiveSpanWholeCache1333_0
  · simpa only [adaptiveSpanLevel1333, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1333_1 adaptiveSpanWholeCache1333_1
  · simpa only [adaptiveSpanLevel1333, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1333_2 adaptiveSpanWholeCache1333_2
  · simpa only [adaptiveSpanLevel1333, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1333_3 adaptiveSpanWholeCache1333_3
  · simpa only [adaptiveSpanLevel1333, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1333_4 adaptiveSpanWholeCache1333_4
  · simpa only [adaptiveSpanLevel1333, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1333_5 adaptiveSpanWholeCache1333_5

theorem adaptiveSpanTreeRepresents1333 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1333.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1333 (halfOdds 1333)
      (sharpDegree (1311 / 2) 6 (adaptiveSpanNumerator1333 s) (adaptiveSpanDenominator1333 s))
      (sharpDegree 1311 6 (adaptiveSpanNumerator1333 s) (adaptiveSpanDenominator1333 s))
      (adaptiveSpanLevel1333 s).1 (adaptiveSpanLevel1333 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1333, adaptiveSpanNumerator1333, adaptiveSpanDenominator1333, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 667) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1333 adaptiveOrder1333 adaptiveSpanNumericCheck1333_0
        adaptiveSpanEven1333_0 adaptiveSpanWhole1333_0
        adaptiveSpanEvenEntries1333_0 adaptiveSpanWholeEntries1333_0
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanEvenDomain1333_0)
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanWholeDomain1333_0)
  · simpa only [adaptiveSpanLevel1333, adaptiveSpanNumerator1333, adaptiveSpanDenominator1333, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 667) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1333 adaptiveOrder1333 adaptiveSpanNumericCheck1333_1
        adaptiveSpanEven1333_1 adaptiveSpanWhole1333_1
        adaptiveSpanEvenEntries1333_1 adaptiveSpanWholeEntries1333_1
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanEvenDomain1333_1)
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanWholeDomain1333_1)
  · simpa only [adaptiveSpanLevel1333, adaptiveSpanNumerator1333, adaptiveSpanDenominator1333, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 667) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1333 adaptiveOrder1333 adaptiveSpanNumericCheck1333_2
        adaptiveSpanEven1333_2 adaptiveSpanWhole1333_2
        adaptiveSpanEvenEntries1333_2 adaptiveSpanWholeEntries1333_2
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanEvenDomain1333_2)
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanWholeDomain1333_2)
  · simpa only [adaptiveSpanLevel1333, adaptiveSpanNumerator1333, adaptiveSpanDenominator1333, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 667) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1333 adaptiveOrder1333 adaptiveSpanNumericCheck1333_3
        adaptiveSpanEven1333_3 adaptiveSpanWhole1333_3
        adaptiveSpanEvenEntries1333_3 adaptiveSpanWholeEntries1333_3
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanEvenDomain1333_3)
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanWholeDomain1333_3)
  · simpa only [adaptiveSpanLevel1333, adaptiveSpanNumerator1333, adaptiveSpanDenominator1333, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 667) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1333 adaptiveOrder1333 adaptiveSpanNumericCheck1333_4
        adaptiveSpanEven1333_4 adaptiveSpanWhole1333_4
        adaptiveSpanEvenEntries1333_4 adaptiveSpanWholeEntries1333_4
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanEvenDomain1333_4)
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanWholeDomain1333_4)
  · simpa only [adaptiveSpanLevel1333, adaptiveSpanNumerator1333, adaptiveSpanDenominator1333, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 667) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1333 adaptiveOrder1333 adaptiveSpanNumericCheck1333_5
        adaptiveSpanEven1333_5 adaptiveSpanWhole1333_5
        adaptiveSpanEvenEntries1333_5 adaptiveSpanWholeEntries1333_5
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanEvenDomain1333_5)
        (by rw [adaptiveSpanProfileLength1333]; exact adaptiveSpanWholeDomain1333_5)

/-- The complete finite histogram certificate for 1311 ≤ n ≤ 1333. -/
theorem adaptiveSpanHistogram1333 : DegreeIntervalCertificate 1333 adaptiveSpanPrimes1333
    (fun s v => sharpDegree (1311 / 2) 6 (adaptiveSpanNumerator1333 s)
      (adaptiveSpanDenominator1333 s) (totientDensity v))
    (fun s v => sharpDegree 1311 6 (adaptiveSpanNumerator1333 s)
      (adaptiveSpanDenominator1333 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1333)
    adaptiveSpanPrimes1333
    (fun s => sharpDegree (1311 / 2) 6 (adaptiveSpanNumerator1333 s) (adaptiveSpanDenominator1333 s))
    (fun s => sharpDegree 1311 6 (adaptiveSpanNumerator1333 s) (adaptiveSpanDenominator1333 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1333 adaptiveOrder1333 (coreOrderPermutationCheck_sound adaptivePermutation1333)
    (by rw [adaptiveSpanProfileLength1333]; decide +kernel)
    adaptiveSpanLevel1333 adaptiveSpanTreeCache1333 adaptiveSpanTreeRepresents1333
    (fun j => adaptiveSpanWitness1333.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1333

/-- Every required odd cycle for a dense set, throughout 1311 ≤ n ≤ 1333. -/
theorem adaptiveSpanInterval1333 {n : ℕ} (hLn : 1311 ≤ n) (hnU : n ≤ 1333)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1333
    adaptiveSpanNumerator1333 adaptiveSpanDenominator1333 adaptiveSpanSharpTail1333
    adaptiveSpanPrimeSupport1333 adaptiveSpanHistogram1333 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1333
#print axioms adaptiveSpanPrimeSupport1333
#print axioms adaptiveSpanHistogram1333
#print axioms adaptiveSpanInterval1333
end Erdos883Verified
