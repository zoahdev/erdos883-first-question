import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1625Metadata
import Erdos883AdaptiveSpan1625Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1625 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1625 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1625 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1625 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1625.length) :
    SharpTailCertificate 1625 (adaptiveSpanPrimes1625.take s)
      (adaptiveSpanNumerator1625 s) (adaptiveSpanDenominator1625 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1625 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1625 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1625 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1625 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1625 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1625 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1625 : ∀ u ∈ oddUniverse 1625,
    ∀ v ∈ oddUniverse 1625, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1625 : AdaptiveProfileRowsValid adaptiveRows1625 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1625

theorem adaptiveSpanProfileLength1625 : adaptiveRows1625.length = halfOdds 1625 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1625)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1625 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1625.length) :
    (adaptiveSpanLevel1625 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1625 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1625, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1625_0 adaptiveSpanWholeCache1625_0
  · simpa only [adaptiveSpanLevel1625, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1625_1 adaptiveSpanWholeCache1625_1
  · simpa only [adaptiveSpanLevel1625, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1625_2 adaptiveSpanWholeCache1625_2
  · simpa only [adaptiveSpanLevel1625, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1625_3 adaptiveSpanWholeCache1625_3
  · simpa only [adaptiveSpanLevel1625, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1625_4 adaptiveSpanWholeCache1625_4
  · simpa only [adaptiveSpanLevel1625, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1625_5 adaptiveSpanWholeCache1625_5

theorem adaptiveSpanTreeRepresents1625 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1625.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1625 (halfOdds 1625)
      (sharpDegree (1586 / 2) 6 (adaptiveSpanNumerator1625 s) (adaptiveSpanDenominator1625 s))
      (sharpDegree 1586 6 (adaptiveSpanNumerator1625 s) (adaptiveSpanDenominator1625 s))
      (adaptiveSpanLevel1625 s).1 (adaptiveSpanLevel1625 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1625, adaptiveSpanNumerator1625, adaptiveSpanDenominator1625, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 813) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1625 adaptiveOrder1625 adaptiveSpanNumericCheck1625_0
        adaptiveSpanEven1625_0 adaptiveSpanWhole1625_0
        adaptiveSpanEvenEntries1625_0 adaptiveSpanWholeEntries1625_0
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanEvenDomain1625_0)
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanWholeDomain1625_0)
  · simpa only [adaptiveSpanLevel1625, adaptiveSpanNumerator1625, adaptiveSpanDenominator1625, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 813) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1625 adaptiveOrder1625 adaptiveSpanNumericCheck1625_1
        adaptiveSpanEven1625_1 adaptiveSpanWhole1625_1
        adaptiveSpanEvenEntries1625_1 adaptiveSpanWholeEntries1625_1
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanEvenDomain1625_1)
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanWholeDomain1625_1)
  · simpa only [adaptiveSpanLevel1625, adaptiveSpanNumerator1625, adaptiveSpanDenominator1625, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 813) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1625 adaptiveOrder1625 adaptiveSpanNumericCheck1625_2
        adaptiveSpanEven1625_2 adaptiveSpanWhole1625_2
        adaptiveSpanEvenEntries1625_2 adaptiveSpanWholeEntries1625_2
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanEvenDomain1625_2)
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanWholeDomain1625_2)
  · simpa only [adaptiveSpanLevel1625, adaptiveSpanNumerator1625, adaptiveSpanDenominator1625, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 813) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1625 adaptiveOrder1625 adaptiveSpanNumericCheck1625_3
        adaptiveSpanEven1625_3 adaptiveSpanWhole1625_3
        adaptiveSpanEvenEntries1625_3 adaptiveSpanWholeEntries1625_3
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanEvenDomain1625_3)
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanWholeDomain1625_3)
  · simpa only [adaptiveSpanLevel1625, adaptiveSpanNumerator1625, adaptiveSpanDenominator1625, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 813) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1625 adaptiveOrder1625 adaptiveSpanNumericCheck1625_4
        adaptiveSpanEven1625_4 adaptiveSpanWhole1625_4
        adaptiveSpanEvenEntries1625_4 adaptiveSpanWholeEntries1625_4
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanEvenDomain1625_4)
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanWholeDomain1625_4)
  · simpa only [adaptiveSpanLevel1625, adaptiveSpanNumerator1625, adaptiveSpanDenominator1625, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 813) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1625 adaptiveOrder1625 adaptiveSpanNumericCheck1625_5
        adaptiveSpanEven1625_5 adaptiveSpanWhole1625_5
        adaptiveSpanEvenEntries1625_5 adaptiveSpanWholeEntries1625_5
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanEvenDomain1625_5)
        (by rw [adaptiveSpanProfileLength1625]; exact adaptiveSpanWholeDomain1625_5)

/-- The complete finite histogram certificate for 1586 ≤ n ≤ 1625. -/
theorem adaptiveSpanHistogram1625 : DegreeIntervalCertificate 1625 adaptiveSpanPrimes1625
    (fun s v => sharpDegree (1586 / 2) 6 (adaptiveSpanNumerator1625 s)
      (adaptiveSpanDenominator1625 s) (totientDensity v))
    (fun s v => sharpDegree 1586 6 (adaptiveSpanNumerator1625 s)
      (adaptiveSpanDenominator1625 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1625)
    adaptiveSpanPrimes1625
    (fun s => sharpDegree (1586 / 2) 6 (adaptiveSpanNumerator1625 s) (adaptiveSpanDenominator1625 s))
    (fun s => sharpDegree 1586 6 (adaptiveSpanNumerator1625 s) (adaptiveSpanDenominator1625 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1625 adaptiveOrder1625 (coreOrderPermutationCheck_sound adaptivePermutation1625)
    (by rw [adaptiveSpanProfileLength1625]; decide +kernel)
    adaptiveSpanLevel1625 adaptiveSpanTreeCache1625 adaptiveSpanTreeRepresents1625
    (fun j => adaptiveSpanWitness1625.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1625

/-- Every required odd cycle for a dense set, throughout 1586 ≤ n ≤ 1625. -/
theorem adaptiveSpanInterval1625 {n : ℕ} (hLn : 1586 ≤ n) (hnU : n ≤ 1625)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1625
    adaptiveSpanNumerator1625 adaptiveSpanDenominator1625 adaptiveSpanSharpTail1625
    adaptiveSpanPrimeSupport1625 adaptiveSpanHistogram1625 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1625
#print axioms adaptiveSpanPrimeSupport1625
#print axioms adaptiveSpanHistogram1625
#print axioms adaptiveSpanInterval1625
end Erdos883Verified
