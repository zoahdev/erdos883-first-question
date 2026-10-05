import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate5986Metadata
import Erdos883AdaptiveSpan5986Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes5986 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator5986 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | _ => 288

def adaptiveSpanDenominator5986 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | _ => 323

theorem adaptiveSpanSharpTail5986 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5986.length) :
    SharpTailCertificate 5986 (adaptiveSpanPrimes5986.take s)
      (adaptiveSpanNumerator5986 s) (adaptiveSpanDenominator5986 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 5986 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5986 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5986 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5986 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5986 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 5986 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport5986 : ∀ u ∈ oddUniverse 5986,
    ∀ v ∈ oddUniverse 5986, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid5986 : AdaptiveProfileRowsValid adaptiveRows5986 :=
  coreProfileMetadataCheck_sound adaptiveMetadata5986

theorem adaptiveSpanProfileLength5986 : adaptiveRows5986.length = halfOdds 5986 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation5986)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache5986 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5986.length) :
    (adaptiveSpanLevel5986 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel5986 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel5986, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5986_0 adaptiveSpanWholeCache5986_0
  · simpa only [adaptiveSpanLevel5986, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5986_1 adaptiveSpanWholeCache5986_1
  · simpa only [adaptiveSpanLevel5986, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5986_2 adaptiveSpanWholeCache5986_2
  · simpa only [adaptiveSpanLevel5986, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5986_3 adaptiveSpanWholeCache5986_3
  · simpa only [adaptiveSpanLevel5986, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5986_4 adaptiveSpanWholeCache5986_4
  · simpa only [adaptiveSpanLevel5986, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache5986_5 adaptiveSpanWholeCache5986_5

theorem adaptiveSpanTreeRepresents5986 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes5986.length) :
    AdaptiveSpanTreeRepresents adaptiveRows5986 (halfOdds 5986)
      (sharpDegree (5701 / 2) 7 (adaptiveSpanNumerator5986 s) (adaptiveSpanDenominator5986 s))
      (sharpDegree 5701 7 (adaptiveSpanNumerator5986 s) (adaptiveSpanDenominator5986 s))
      (adaptiveSpanLevel5986 s).1 (adaptiveSpanLevel5986 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel5986, adaptiveSpanNumerator5986, adaptiveSpanDenominator5986, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2993) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid5986 adaptiveOrder5986 adaptiveSpanNumericCheck5986_0
        adaptiveSpanEven5986_0 adaptiveSpanWhole5986_0
        adaptiveSpanEvenEntries5986_0 adaptiveSpanWholeEntries5986_0
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanEvenDomain5986_0)
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanWholeDomain5986_0)
  · simpa only [adaptiveSpanLevel5986, adaptiveSpanNumerator5986, adaptiveSpanDenominator5986, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2993) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid5986 adaptiveOrder5986 adaptiveSpanNumericCheck5986_1
        adaptiveSpanEven5986_1 adaptiveSpanWhole5986_1
        adaptiveSpanEvenEntries5986_1 adaptiveSpanWholeEntries5986_1
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanEvenDomain5986_1)
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanWholeDomain5986_1)
  · simpa only [adaptiveSpanLevel5986, adaptiveSpanNumerator5986, adaptiveSpanDenominator5986, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2993) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid5986 adaptiveOrder5986 adaptiveSpanNumericCheck5986_2
        adaptiveSpanEven5986_2 adaptiveSpanWhole5986_2
        adaptiveSpanEvenEntries5986_2 adaptiveSpanWholeEntries5986_2
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanEvenDomain5986_2)
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanWholeDomain5986_2)
  · simpa only [adaptiveSpanLevel5986, adaptiveSpanNumerator5986, adaptiveSpanDenominator5986, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2993) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid5986 adaptiveOrder5986 adaptiveSpanNumericCheck5986_3
        adaptiveSpanEven5986_3 adaptiveSpanWhole5986_3
        adaptiveSpanEvenEntries5986_3 adaptiveSpanWholeEntries5986_3
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanEvenDomain5986_3)
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanWholeDomain5986_3)
  · simpa only [adaptiveSpanLevel5986, adaptiveSpanNumerator5986, adaptiveSpanDenominator5986, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2993) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid5986 adaptiveOrder5986 adaptiveSpanNumericCheck5986_4
        adaptiveSpanEven5986_4 adaptiveSpanWhole5986_4
        adaptiveSpanEvenEntries5986_4 adaptiveSpanWholeEntries5986_4
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanEvenDomain5986_4)
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanWholeDomain5986_4)
  · simpa only [adaptiveSpanLevel5986, adaptiveSpanNumerator5986, adaptiveSpanDenominator5986, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2993) (by decide : 0 < 323)
        adaptiveSpanProfilesValid5986 adaptiveOrder5986 adaptiveSpanNumericCheck5986_5
        adaptiveSpanEven5986_5 adaptiveSpanWhole5986_5
        adaptiveSpanEvenEntries5986_5 adaptiveSpanWholeEntries5986_5
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanEvenDomain5986_5)
        (by rw [adaptiveSpanProfileLength5986]; exact adaptiveSpanWholeDomain5986_5)

/-- The complete finite histogram certificate for 5701 ≤ n ≤ 5986. -/
theorem adaptiveSpanHistogram5986 : DegreeIntervalCertificate 5986 adaptiveSpanPrimes5986
    (fun s v => sharpDegree (5701 / 2) 7 (adaptiveSpanNumerator5986 s)
      (adaptiveSpanDenominator5986 s) (totientDensity v))
    (fun s v => sharpDegree 5701 7 (adaptiveSpanNumerator5986 s)
      (adaptiveSpanDenominator5986 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows5986)
    adaptiveSpanPrimes5986
    (fun s => sharpDegree (5701 / 2) 7 (adaptiveSpanNumerator5986 s) (adaptiveSpanDenominator5986 s))
    (fun s => sharpDegree 5701 7 (adaptiveSpanNumerator5986 s) (adaptiveSpanDenominator5986 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid5986 adaptiveOrder5986 (coreOrderPermutationCheck_sound adaptivePermutation5986)
    (by rw [adaptiveSpanProfileLength5986]; decide +kernel)
    adaptiveSpanLevel5986 adaptiveSpanTreeCache5986 adaptiveSpanTreeRepresents5986
    (fun j => adaptiveSpanWitness5986.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck5986

/-- Every required odd cycle for a dense set, throughout 5701 ≤ n ≤ 5986. -/
theorem adaptiveSpanInterval5986 {n : ℕ} (hLn : 5701 ≤ n) (hnU : n ≤ 5986)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes5986
    adaptiveSpanNumerator5986 adaptiveSpanDenominator5986 adaptiveSpanSharpTail5986
    adaptiveSpanPrimeSupport5986 adaptiveSpanHistogram5986 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail5986
#print axioms adaptiveSpanPrimeSupport5986
#print axioms adaptiveSpanHistogram5986
#print axioms adaptiveSpanInterval5986
end Erdos883Verified
