import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate5428Metadata
import Erdos883AdaptiveSpan5428Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes5428 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator5428 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | _ => 288

def adaptiveSpanDenominator5428 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | _ => 323

theorem adaptiveSpanSharpTail5428 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5428.length) :
    SharpTailCertificate 5428 (adaptiveSpanPrimes5428.take s)
      (adaptiveSpanNumerator5428 s) (adaptiveSpanDenominator5428 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 5428 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5428 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5428 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5428 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5428 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5428 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport5428 : ∀ u ∈ oddUniverse 5428,
    ∀ v ∈ oddUniverse 5428, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid5428 : AdaptiveProfileRowsValid adaptiveRows5428 :=
  coreProfileMetadataCheck_sound adaptiveMetadata5428

theorem adaptiveSpanProfileLength5428 : adaptiveRows5428.length = halfOdds 5428 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation5428)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache5428 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5428.length) :
    (adaptiveSpanLevel5428 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel5428 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel5428, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5428_0 adaptiveSpanWholeCache5428_0
  · simpa only [adaptiveSpanLevel5428, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5428_1 adaptiveSpanWholeCache5428_1
  · simpa only [adaptiveSpanLevel5428, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5428_2 adaptiveSpanWholeCache5428_2
  · simpa only [adaptiveSpanLevel5428, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5428_3 adaptiveSpanWholeCache5428_3
  · simpa only [adaptiveSpanLevel5428, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5428_4 adaptiveSpanWholeCache5428_4
  · simpa only [adaptiveSpanLevel5428, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5428_5 adaptiveSpanWholeCache5428_5

theorem adaptiveSpanTreeRepresents5428 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5428.length) :
    AdaptiveSpanTreeRepresents adaptiveRows5428 (halfOdds 5428)
      (sharpDegree (5170 / 2) 7 (adaptiveSpanNumerator5428 s) (adaptiveSpanDenominator5428 s))
      (sharpDegree 5170 7 (adaptiveSpanNumerator5428 s) (adaptiveSpanDenominator5428 s))
      (adaptiveSpanLevel5428 s).1 (adaptiveSpanLevel5428 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel5428, adaptiveSpanNumerator5428, adaptiveSpanDenominator5428, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2714) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid5428 adaptiveOrder5428 adaptiveSpanNumericCheck5428_0
        adaptiveSpanEven5428_0 adaptiveSpanWhole5428_0
        adaptiveSpanEvenEntries5428_0 adaptiveSpanWholeEntries5428_0
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanEvenDomain5428_0)
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanWholeDomain5428_0)
  · simpa only [adaptiveSpanLevel5428, adaptiveSpanNumerator5428, adaptiveSpanDenominator5428, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2714) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid5428 adaptiveOrder5428 adaptiveSpanNumericCheck5428_1
        adaptiveSpanEven5428_1 adaptiveSpanWhole5428_1
        adaptiveSpanEvenEntries5428_1 adaptiveSpanWholeEntries5428_1
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanEvenDomain5428_1)
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanWholeDomain5428_1)
  · simpa only [adaptiveSpanLevel5428, adaptiveSpanNumerator5428, adaptiveSpanDenominator5428, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2714) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid5428 adaptiveOrder5428 adaptiveSpanNumericCheck5428_2
        adaptiveSpanEven5428_2 adaptiveSpanWhole5428_2
        adaptiveSpanEvenEntries5428_2 adaptiveSpanWholeEntries5428_2
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanEvenDomain5428_2)
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanWholeDomain5428_2)
  · simpa only [adaptiveSpanLevel5428, adaptiveSpanNumerator5428, adaptiveSpanDenominator5428, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2714) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid5428 adaptiveOrder5428 adaptiveSpanNumericCheck5428_3
        adaptiveSpanEven5428_3 adaptiveSpanWhole5428_3
        adaptiveSpanEvenEntries5428_3 adaptiveSpanWholeEntries5428_3
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanEvenDomain5428_3)
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanWholeDomain5428_3)
  · simpa only [adaptiveSpanLevel5428, adaptiveSpanNumerator5428, adaptiveSpanDenominator5428, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2714) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid5428 adaptiveOrder5428 adaptiveSpanNumericCheck5428_4
        adaptiveSpanEven5428_4 adaptiveSpanWhole5428_4
        adaptiveSpanEvenEntries5428_4 adaptiveSpanWholeEntries5428_4
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanEvenDomain5428_4)
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanWholeDomain5428_4)
  · simpa only [adaptiveSpanLevel5428, adaptiveSpanNumerator5428, adaptiveSpanDenominator5428, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2714) (by decide : 0 < 323)
        adaptiveSpanProfilesValid5428 adaptiveOrder5428 adaptiveSpanNumericCheck5428_5
        adaptiveSpanEven5428_5 adaptiveSpanWhole5428_5
        adaptiveSpanEvenEntries5428_5 adaptiveSpanWholeEntries5428_5
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanEvenDomain5428_5)
        (by rw [adaptiveSpanProfileLength5428]; exact adaptiveSpanWholeDomain5428_5)

/-- The complete finite histogram certificate for 5170 ≤ n ≤ 5428. -/
theorem adaptiveSpanHistogram5428 : DegreeIntervalCertificate 5428 adaptiveSpanPrimes5428
    (fun s v => sharpDegree (5170 / 2) 7 (adaptiveSpanNumerator5428 s)
      (adaptiveSpanDenominator5428 s) (totientDensity v))
    (fun s v => sharpDegree 5170 7 (adaptiveSpanNumerator5428 s)
      (adaptiveSpanDenominator5428 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows5428)
    adaptiveSpanPrimes5428
    (fun s => sharpDegree (5170 / 2) 7 (adaptiveSpanNumerator5428 s) (adaptiveSpanDenominator5428 s))
    (fun s => sharpDegree 5170 7 (adaptiveSpanNumerator5428 s) (adaptiveSpanDenominator5428 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid5428 adaptiveOrder5428 (coreOrderPermutationCheck_sound adaptivePermutation5428)
    (by rw [adaptiveSpanProfileLength5428]; decide +kernel)
    adaptiveSpanLevel5428 adaptiveSpanTreeCache5428 adaptiveSpanTreeRepresents5428
    (fun j => adaptiveSpanWitness5428.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck5428

/-- Every required odd cycle for a dense set, throughout 5170 ≤ n ≤ 5428. -/
theorem adaptiveSpanInterval5428 {n : ℕ} (hLn : 5170 ≤ n) (hnU : n ≤ 5428)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes5428
    adaptiveSpanNumerator5428 adaptiveSpanDenominator5428 adaptiveSpanSharpTail5428
    adaptiveSpanPrimeSupport5428 adaptiveSpanHistogram5428 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail5428
#print axioms adaptiveSpanPrimeSupport5428
#print axioms adaptiveSpanHistogram5428
#print axioms adaptiveSpanInterval5428
end Erdos883Verified
