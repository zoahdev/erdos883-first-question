import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1310Metadata
import Erdos883AdaptiveSpan1310Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1310 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1310 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1310 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1310 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1310.length) :
    SharpTailCertificate 1310 (adaptiveSpanPrimes1310.take s)
      (adaptiveSpanNumerator1310 s) (adaptiveSpanDenominator1310 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1310 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1310 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1310 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1310 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1310 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1310 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1310 : ∀ u ∈ oddUniverse 1310,
    ∀ v ∈ oddUniverse 1310, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1310 : AdaptiveProfileRowsValid adaptiveRows1310 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1310

theorem adaptiveSpanProfileLength1310 : adaptiveRows1310.length = halfOdds 1310 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1310)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1310 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1310.length) :
    (adaptiveSpanLevel1310 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1310 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1310, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1310_0 adaptiveSpanWholeCache1310_0
  · simpa only [adaptiveSpanLevel1310, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1310_1 adaptiveSpanWholeCache1310_1
  · simpa only [adaptiveSpanLevel1310, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1310_2 adaptiveSpanWholeCache1310_2
  · simpa only [adaptiveSpanLevel1310, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1310_3 adaptiveSpanWholeCache1310_3
  · simpa only [adaptiveSpanLevel1310, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1310_4 adaptiveSpanWholeCache1310_4
  · simpa only [adaptiveSpanLevel1310, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1310_5 adaptiveSpanWholeCache1310_5

theorem adaptiveSpanTreeRepresents1310 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1310.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1310 (halfOdds 1310)
      (sharpDegree (1287 / 2) 6 (adaptiveSpanNumerator1310 s) (adaptiveSpanDenominator1310 s))
      (sharpDegree 1287 6 (adaptiveSpanNumerator1310 s) (adaptiveSpanDenominator1310 s))
      (adaptiveSpanLevel1310 s).1 (adaptiveSpanLevel1310 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1310, adaptiveSpanNumerator1310, adaptiveSpanDenominator1310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 655) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1310 adaptiveOrder1310 adaptiveSpanNumericCheck1310_0
        adaptiveSpanEven1310_0 adaptiveSpanWhole1310_0
        adaptiveSpanEvenEntries1310_0 adaptiveSpanWholeEntries1310_0
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanEvenDomain1310_0)
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanWholeDomain1310_0)
  · simpa only [adaptiveSpanLevel1310, adaptiveSpanNumerator1310, adaptiveSpanDenominator1310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 655) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1310 adaptiveOrder1310 adaptiveSpanNumericCheck1310_1
        adaptiveSpanEven1310_1 adaptiveSpanWhole1310_1
        adaptiveSpanEvenEntries1310_1 adaptiveSpanWholeEntries1310_1
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanEvenDomain1310_1)
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanWholeDomain1310_1)
  · simpa only [adaptiveSpanLevel1310, adaptiveSpanNumerator1310, adaptiveSpanDenominator1310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 655) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1310 adaptiveOrder1310 adaptiveSpanNumericCheck1310_2
        adaptiveSpanEven1310_2 adaptiveSpanWhole1310_2
        adaptiveSpanEvenEntries1310_2 adaptiveSpanWholeEntries1310_2
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanEvenDomain1310_2)
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanWholeDomain1310_2)
  · simpa only [adaptiveSpanLevel1310, adaptiveSpanNumerator1310, adaptiveSpanDenominator1310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 655) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1310 adaptiveOrder1310 adaptiveSpanNumericCheck1310_3
        adaptiveSpanEven1310_3 adaptiveSpanWhole1310_3
        adaptiveSpanEvenEntries1310_3 adaptiveSpanWholeEntries1310_3
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanEvenDomain1310_3)
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanWholeDomain1310_3)
  · simpa only [adaptiveSpanLevel1310, adaptiveSpanNumerator1310, adaptiveSpanDenominator1310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 655) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1310 adaptiveOrder1310 adaptiveSpanNumericCheck1310_4
        adaptiveSpanEven1310_4 adaptiveSpanWhole1310_4
        adaptiveSpanEvenEntries1310_4 adaptiveSpanWholeEntries1310_4
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanEvenDomain1310_4)
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanWholeDomain1310_4)
  · simpa only [adaptiveSpanLevel1310, adaptiveSpanNumerator1310, adaptiveSpanDenominator1310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 655) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1310 adaptiveOrder1310 adaptiveSpanNumericCheck1310_5
        adaptiveSpanEven1310_5 adaptiveSpanWhole1310_5
        adaptiveSpanEvenEntries1310_5 adaptiveSpanWholeEntries1310_5
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanEvenDomain1310_5)
        (by rw [adaptiveSpanProfileLength1310]; exact adaptiveSpanWholeDomain1310_5)

/-- The complete finite histogram certificate for 1287 ≤ n ≤ 1310. -/
theorem adaptiveSpanHistogram1310 : DegreeIntervalCertificate 1310 adaptiveSpanPrimes1310
    (fun s v => sharpDegree (1287 / 2) 6 (adaptiveSpanNumerator1310 s)
      (adaptiveSpanDenominator1310 s) (totientDensity v))
    (fun s v => sharpDegree 1287 6 (adaptiveSpanNumerator1310 s)
      (adaptiveSpanDenominator1310 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1310)
    adaptiveSpanPrimes1310
    (fun s => sharpDegree (1287 / 2) 6 (adaptiveSpanNumerator1310 s) (adaptiveSpanDenominator1310 s))
    (fun s => sharpDegree 1287 6 (adaptiveSpanNumerator1310 s) (adaptiveSpanDenominator1310 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1310 adaptiveOrder1310 (coreOrderPermutationCheck_sound adaptivePermutation1310)
    (by rw [adaptiveSpanProfileLength1310]; decide +kernel)
    adaptiveSpanLevel1310 adaptiveSpanTreeCache1310 adaptiveSpanTreeRepresents1310
    (fun j => adaptiveSpanWitness1310.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1310

/-- Every required odd cycle for a dense set, throughout 1287 ≤ n ≤ 1310. -/
theorem adaptiveSpanInterval1310 {n : ℕ} (hLn : 1287 ≤ n) (hnU : n ≤ 1310)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1310
    adaptiveSpanNumerator1310 adaptiveSpanDenominator1310 adaptiveSpanSharpTail1310
    adaptiveSpanPrimeSupport1310 adaptiveSpanHistogram1310 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1310
#print axioms adaptiveSpanPrimeSupport1310
#print axioms adaptiveSpanHistogram1310
#print axioms adaptiveSpanInterval1310
end Erdos883Verified
