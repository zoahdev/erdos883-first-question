import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate5169Metadata
import Erdos883AdaptiveSpan5169Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes5169 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator5169 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | _ => 288

def adaptiveSpanDenominator5169 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | _ => 323

theorem adaptiveSpanSharpTail5169 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5169.length) :
    SharpTailCertificate 5169 (adaptiveSpanPrimes5169.take s)
      (adaptiveSpanNumerator5169 s) (adaptiveSpanDenominator5169 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 5169 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5169 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5169 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5169 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5169 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5169 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport5169 : ∀ u ∈ oddUniverse 5169,
    ∀ v ∈ oddUniverse 5169, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid5169 : AdaptiveProfileRowsValid adaptiveRows5169 :=
  coreProfileMetadataCheck_sound adaptiveMetadata5169

theorem adaptiveSpanProfileLength5169 : adaptiveRows5169.length = halfOdds 5169 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation5169)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache5169 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5169.length) :
    (adaptiveSpanLevel5169 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel5169 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel5169, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5169_0 adaptiveSpanWholeCache5169_0
  · simpa only [adaptiveSpanLevel5169, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5169_1 adaptiveSpanWholeCache5169_1
  · simpa only [adaptiveSpanLevel5169, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5169_2 adaptiveSpanWholeCache5169_2
  · simpa only [adaptiveSpanLevel5169, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5169_3 adaptiveSpanWholeCache5169_3
  · simpa only [adaptiveSpanLevel5169, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5169_4 adaptiveSpanWholeCache5169_4
  · simpa only [adaptiveSpanLevel5169, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5169_5 adaptiveSpanWholeCache5169_5

theorem adaptiveSpanTreeRepresents5169 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5169.length) :
    AdaptiveSpanTreeRepresents adaptiveRows5169 (halfOdds 5169)
      (sharpDegree (4923 / 2) 7 (adaptiveSpanNumerator5169 s) (adaptiveSpanDenominator5169 s))
      (sharpDegree 4923 7 (adaptiveSpanNumerator5169 s) (adaptiveSpanDenominator5169 s))
      (adaptiveSpanLevel5169 s).1 (adaptiveSpanLevel5169 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel5169, adaptiveSpanNumerator5169, adaptiveSpanDenominator5169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2585) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid5169 adaptiveOrder5169 adaptiveSpanNumericCheck5169_0
        adaptiveSpanEven5169_0 adaptiveSpanWhole5169_0
        adaptiveSpanEvenEntries5169_0 adaptiveSpanWholeEntries5169_0
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanEvenDomain5169_0)
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanWholeDomain5169_0)
  · simpa only [adaptiveSpanLevel5169, adaptiveSpanNumerator5169, adaptiveSpanDenominator5169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2585) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid5169 adaptiveOrder5169 adaptiveSpanNumericCheck5169_1
        adaptiveSpanEven5169_1 adaptiveSpanWhole5169_1
        adaptiveSpanEvenEntries5169_1 adaptiveSpanWholeEntries5169_1
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanEvenDomain5169_1)
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanWholeDomain5169_1)
  · simpa only [adaptiveSpanLevel5169, adaptiveSpanNumerator5169, adaptiveSpanDenominator5169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2585) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid5169 adaptiveOrder5169 adaptiveSpanNumericCheck5169_2
        adaptiveSpanEven5169_2 adaptiveSpanWhole5169_2
        adaptiveSpanEvenEntries5169_2 adaptiveSpanWholeEntries5169_2
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanEvenDomain5169_2)
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanWholeDomain5169_2)
  · simpa only [adaptiveSpanLevel5169, adaptiveSpanNumerator5169, adaptiveSpanDenominator5169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2585) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid5169 adaptiveOrder5169 adaptiveSpanNumericCheck5169_3
        adaptiveSpanEven5169_3 adaptiveSpanWhole5169_3
        adaptiveSpanEvenEntries5169_3 adaptiveSpanWholeEntries5169_3
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanEvenDomain5169_3)
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanWholeDomain5169_3)
  · simpa only [adaptiveSpanLevel5169, adaptiveSpanNumerator5169, adaptiveSpanDenominator5169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2585) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid5169 adaptiveOrder5169 adaptiveSpanNumericCheck5169_4
        adaptiveSpanEven5169_4 adaptiveSpanWhole5169_4
        adaptiveSpanEvenEntries5169_4 adaptiveSpanWholeEntries5169_4
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanEvenDomain5169_4)
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanWholeDomain5169_4)
  · simpa only [adaptiveSpanLevel5169, adaptiveSpanNumerator5169, adaptiveSpanDenominator5169, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2585) (by decide : 0 < 323)
        adaptiveSpanProfilesValid5169 adaptiveOrder5169 adaptiveSpanNumericCheck5169_5
        adaptiveSpanEven5169_5 adaptiveSpanWhole5169_5
        adaptiveSpanEvenEntries5169_5 adaptiveSpanWholeEntries5169_5
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanEvenDomain5169_5)
        (by rw [adaptiveSpanProfileLength5169]; exact adaptiveSpanWholeDomain5169_5)

/-- The complete finite histogram certificate for 4923 ≤ n ≤ 5169. -/
theorem adaptiveSpanHistogram5169 : DegreeIntervalCertificate 5169 adaptiveSpanPrimes5169
    (fun s v => sharpDegree (4923 / 2) 7 (adaptiveSpanNumerator5169 s)
      (adaptiveSpanDenominator5169 s) (totientDensity v))
    (fun s v => sharpDegree 4923 7 (adaptiveSpanNumerator5169 s)
      (adaptiveSpanDenominator5169 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows5169)
    adaptiveSpanPrimes5169
    (fun s => sharpDegree (4923 / 2) 7 (adaptiveSpanNumerator5169 s) (adaptiveSpanDenominator5169 s))
    (fun s => sharpDegree 4923 7 (adaptiveSpanNumerator5169 s) (adaptiveSpanDenominator5169 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid5169 adaptiveOrder5169 (coreOrderPermutationCheck_sound adaptivePermutation5169)
    (by rw [adaptiveSpanProfileLength5169]; decide +kernel)
    adaptiveSpanLevel5169 adaptiveSpanTreeCache5169 adaptiveSpanTreeRepresents5169
    (fun j => adaptiveSpanWitness5169.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck5169

/-- Every required odd cycle for a dense set, throughout 4923 ≤ n ≤ 5169. -/
theorem adaptiveSpanInterval5169 {n : ℕ} (hLn : 4923 ≤ n) (hnU : n ≤ 5169)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes5169
    adaptiveSpanNumerator5169 adaptiveSpanDenominator5169 adaptiveSpanSharpTail5169
    adaptiveSpanPrimeSupport5169 adaptiveSpanHistogram5169 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail5169
#print axioms adaptiveSpanPrimeSupport5169
#print axioms adaptiveSpanHistogram5169
#print axioms adaptiveSpanInterval5169
end Erdos883Verified
