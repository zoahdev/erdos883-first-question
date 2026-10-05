import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate5700Metadata
import Erdos883AdaptiveSpan5700Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes5700 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator5700 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | _ => 288

def adaptiveSpanDenominator5700 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | _ => 323

theorem adaptiveSpanSharpTail5700 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5700.length) :
    SharpTailCertificate 5700 (adaptiveSpanPrimes5700.take s)
      (adaptiveSpanNumerator5700 s) (adaptiveSpanDenominator5700 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 5700 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5700 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5700 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5700 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5700 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5700 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport5700 : ∀ u ∈ oddUniverse 5700,
    ∀ v ∈ oddUniverse 5700, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid5700 : AdaptiveProfileRowsValid adaptiveRows5700 :=
  coreProfileMetadataCheck_sound adaptiveMetadata5700

theorem adaptiveSpanProfileLength5700 : adaptiveRows5700.length = halfOdds 5700 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation5700)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache5700 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5700.length) :
    (adaptiveSpanLevel5700 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel5700 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel5700, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5700_0 adaptiveSpanWholeCache5700_0
  · simpa only [adaptiveSpanLevel5700, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5700_1 adaptiveSpanWholeCache5700_1
  · simpa only [adaptiveSpanLevel5700, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5700_2 adaptiveSpanWholeCache5700_2
  · simpa only [adaptiveSpanLevel5700, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5700_3 adaptiveSpanWholeCache5700_3
  · simpa only [adaptiveSpanLevel5700, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5700_4 adaptiveSpanWholeCache5700_4
  · simpa only [adaptiveSpanLevel5700, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5700_5 adaptiveSpanWholeCache5700_5

theorem adaptiveSpanTreeRepresents5700 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5700.length) :
    AdaptiveSpanTreeRepresents adaptiveRows5700 (halfOdds 5700)
      (sharpDegree (5429 / 2) 7 (adaptiveSpanNumerator5700 s) (adaptiveSpanDenominator5700 s))
      (sharpDegree 5429 7 (adaptiveSpanNumerator5700 s) (adaptiveSpanDenominator5700 s))
      (adaptiveSpanLevel5700 s).1 (adaptiveSpanLevel5700 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel5700, adaptiveSpanNumerator5700, adaptiveSpanDenominator5700, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2850) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid5700 adaptiveOrder5700 adaptiveSpanNumericCheck5700_0
        adaptiveSpanEven5700_0 adaptiveSpanWhole5700_0
        adaptiveSpanEvenEntries5700_0 adaptiveSpanWholeEntries5700_0
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanEvenDomain5700_0)
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanWholeDomain5700_0)
  · simpa only [adaptiveSpanLevel5700, adaptiveSpanNumerator5700, adaptiveSpanDenominator5700, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2850) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid5700 adaptiveOrder5700 adaptiveSpanNumericCheck5700_1
        adaptiveSpanEven5700_1 adaptiveSpanWhole5700_1
        adaptiveSpanEvenEntries5700_1 adaptiveSpanWholeEntries5700_1
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanEvenDomain5700_1)
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanWholeDomain5700_1)
  · simpa only [adaptiveSpanLevel5700, adaptiveSpanNumerator5700, adaptiveSpanDenominator5700, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2850) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid5700 adaptiveOrder5700 adaptiveSpanNumericCheck5700_2
        adaptiveSpanEven5700_2 adaptiveSpanWhole5700_2
        adaptiveSpanEvenEntries5700_2 adaptiveSpanWholeEntries5700_2
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanEvenDomain5700_2)
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanWholeDomain5700_2)
  · simpa only [adaptiveSpanLevel5700, adaptiveSpanNumerator5700, adaptiveSpanDenominator5700, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2850) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid5700 adaptiveOrder5700 adaptiveSpanNumericCheck5700_3
        adaptiveSpanEven5700_3 adaptiveSpanWhole5700_3
        adaptiveSpanEvenEntries5700_3 adaptiveSpanWholeEntries5700_3
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanEvenDomain5700_3)
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanWholeDomain5700_3)
  · simpa only [adaptiveSpanLevel5700, adaptiveSpanNumerator5700, adaptiveSpanDenominator5700, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2850) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid5700 adaptiveOrder5700 adaptiveSpanNumericCheck5700_4
        adaptiveSpanEven5700_4 adaptiveSpanWhole5700_4
        adaptiveSpanEvenEntries5700_4 adaptiveSpanWholeEntries5700_4
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanEvenDomain5700_4)
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanWholeDomain5700_4)
  · simpa only [adaptiveSpanLevel5700, adaptiveSpanNumerator5700, adaptiveSpanDenominator5700, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2850) (by decide : 0 < 323)
        adaptiveSpanProfilesValid5700 adaptiveOrder5700 adaptiveSpanNumericCheck5700_5
        adaptiveSpanEven5700_5 adaptiveSpanWhole5700_5
        adaptiveSpanEvenEntries5700_5 adaptiveSpanWholeEntries5700_5
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanEvenDomain5700_5)
        (by rw [adaptiveSpanProfileLength5700]; exact adaptiveSpanWholeDomain5700_5)

/-- The complete finite histogram certificate for 5429 ≤ n ≤ 5700. -/
theorem adaptiveSpanHistogram5700 : DegreeIntervalCertificate 5700 adaptiveSpanPrimes5700
    (fun s v => sharpDegree (5429 / 2) 7 (adaptiveSpanNumerator5700 s)
      (adaptiveSpanDenominator5700 s) (totientDensity v))
    (fun s v => sharpDegree 5429 7 (adaptiveSpanNumerator5700 s)
      (adaptiveSpanDenominator5700 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows5700)
    adaptiveSpanPrimes5700
    (fun s => sharpDegree (5429 / 2) 7 (adaptiveSpanNumerator5700 s) (adaptiveSpanDenominator5700 s))
    (fun s => sharpDegree 5429 7 (adaptiveSpanNumerator5700 s) (adaptiveSpanDenominator5700 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid5700 adaptiveOrder5700 (coreOrderPermutationCheck_sound adaptivePermutation5700)
    (by rw [adaptiveSpanProfileLength5700]; decide +kernel)
    adaptiveSpanLevel5700 adaptiveSpanTreeCache5700 adaptiveSpanTreeRepresents5700
    (fun j => adaptiveSpanWitness5700.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck5700

/-- Every required odd cycle for a dense set, throughout 5429 ≤ n ≤ 5700. -/
theorem adaptiveSpanInterval5700 {n : ℕ} (hLn : 5429 ≤ n) (hnU : n ≤ 5700)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes5700
    adaptiveSpanNumerator5700 adaptiveSpanDenominator5700 adaptiveSpanSharpTail5700
    adaptiveSpanPrimeSupport5700 adaptiveSpanHistogram5700 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail5700
#print axioms adaptiveSpanPrimeSupport5700
#print axioms adaptiveSpanHistogram5700
#print axioms adaptiveSpanInterval5700
end Erdos883Verified
