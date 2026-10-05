import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate30284Metadata
import Erdos883AdaptiveSpan30284Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate30284PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes30284 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator30284 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 840

def adaptiveSpanDenominator30284 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 899

theorem adaptiveSpanSharpTail30284 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes30284.length) :
    SharpTailCertificate 30284 (adaptiveSpanPrimes30284.take s)
      (adaptiveSpanNumerator30284 s) (adaptiveSpanDenominator30284 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 30284 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 30284 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 30284 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 30284 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 30284 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 30284 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 30284 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 30284 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 30284 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport30284 : ∀ u ∈ oddUniverse 30284,
    ∀ v ∈ oddUniverse 30284, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid30284 : AdaptiveProfileRowsValid adaptiveRows30284 :=
  coreProfileMetadataCheck_sound adaptiveMetadata30284

theorem adaptiveSpanProfileLength30284 : adaptiveRows30284.length = halfOdds 30284 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics30284
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache30284 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes30284.length) :
    (adaptiveSpanLevel30284 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel30284 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel30284, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache30284_0 adaptiveSpanWholeCache30284_0
  · simpa only [adaptiveSpanLevel30284, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache30284_1 adaptiveSpanWholeCache30284_1
  · simpa only [adaptiveSpanLevel30284, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache30284_2 adaptiveSpanWholeCache30284_2
  · simpa only [adaptiveSpanLevel30284, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache30284_3 adaptiveSpanWholeCache30284_3
  · simpa only [adaptiveSpanLevel30284, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache30284_4 adaptiveSpanWholeCache30284_4
  · simpa only [adaptiveSpanLevel30284, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache30284_5 adaptiveSpanWholeCache30284_5
  · simpa only [adaptiveSpanLevel30284, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache30284_6 adaptiveSpanWholeCache30284_6
  · simpa only [adaptiveSpanLevel30284, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache30284_7 adaptiveSpanWholeCache30284_7
  · simpa only [adaptiveSpanLevel30284, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache30284_8 adaptiveSpanWholeCache30284_8

theorem adaptiveSpanTreeRepresents30284 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes30284.length) :
    AdaptiveSpanTreeRepresents adaptiveRows30284 (halfOdds 30284)
      (sharpDegree (27531 / 2) 8 (adaptiveSpanNumerator30284 s) (adaptiveSpanDenominator30284 s))
      (sharpDegree 27531 8 (adaptiveSpanNumerator30284 s) (adaptiveSpanDenominator30284 s))
      (adaptiveSpanLevel30284 s).1 (adaptiveSpanLevel30284 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel30284, adaptiveSpanNumerator30284, adaptiveSpanDenominator30284, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 15142) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid30284 adaptiveOrder30284 adaptiveSpanNumericCheck30284_0
        adaptiveSpanEven30284_0 adaptiveSpanWhole30284_0
        adaptiveSpanEvenEntries30284_0 adaptiveSpanWholeEntries30284_0
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanEvenDomain30284_0)
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanWholeDomain30284_0)
  · simpa only [adaptiveSpanLevel30284, adaptiveSpanNumerator30284, adaptiveSpanDenominator30284, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 15142) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid30284 adaptiveOrder30284 adaptiveSpanNumericCheck30284_1
        adaptiveSpanEven30284_1 adaptiveSpanWhole30284_1
        adaptiveSpanEvenEntries30284_1 adaptiveSpanWholeEntries30284_1
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanEvenDomain30284_1)
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanWholeDomain30284_1)
  · simpa only [adaptiveSpanLevel30284, adaptiveSpanNumerator30284, adaptiveSpanDenominator30284, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 15142) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid30284 adaptiveOrder30284 adaptiveSpanNumericCheck30284_2
        adaptiveSpanEven30284_2 adaptiveSpanWhole30284_2
        adaptiveSpanEvenEntries30284_2 adaptiveSpanWholeEntries30284_2
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanEvenDomain30284_2)
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanWholeDomain30284_2)
  · simpa only [adaptiveSpanLevel30284, adaptiveSpanNumerator30284, adaptiveSpanDenominator30284, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 15142) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid30284 adaptiveOrder30284 adaptiveSpanNumericCheck30284_3
        adaptiveSpanEven30284_3 adaptiveSpanWhole30284_3
        adaptiveSpanEvenEntries30284_3 adaptiveSpanWholeEntries30284_3
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanEvenDomain30284_3)
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanWholeDomain30284_3)
  · simpa only [adaptiveSpanLevel30284, adaptiveSpanNumerator30284, adaptiveSpanDenominator30284, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 15142) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid30284 adaptiveOrder30284 adaptiveSpanNumericCheck30284_4
        adaptiveSpanEven30284_4 adaptiveSpanWhole30284_4
        adaptiveSpanEvenEntries30284_4 adaptiveSpanWholeEntries30284_4
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanEvenDomain30284_4)
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanWholeDomain30284_4)
  · simpa only [adaptiveSpanLevel30284, adaptiveSpanNumerator30284, adaptiveSpanDenominator30284, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 15142) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid30284 adaptiveOrder30284 adaptiveSpanNumericCheck30284_5
        adaptiveSpanEven30284_5 adaptiveSpanWhole30284_5
        adaptiveSpanEvenEntries30284_5 adaptiveSpanWholeEntries30284_5
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanEvenDomain30284_5)
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanWholeDomain30284_5)
  · simpa only [adaptiveSpanLevel30284, adaptiveSpanNumerator30284, adaptiveSpanDenominator30284, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 15142) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid30284 adaptiveOrder30284 adaptiveSpanNumericCheck30284_6
        adaptiveSpanEven30284_6 adaptiveSpanWhole30284_6
        adaptiveSpanEvenEntries30284_6 adaptiveSpanWholeEntries30284_6
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanEvenDomain30284_6)
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanWholeDomain30284_6)
  · simpa only [adaptiveSpanLevel30284, adaptiveSpanNumerator30284, adaptiveSpanDenominator30284, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 15142) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid30284 adaptiveOrder30284 adaptiveSpanNumericCheck30284_7
        adaptiveSpanEven30284_7 adaptiveSpanWhole30284_7
        adaptiveSpanEvenEntries30284_7 adaptiveSpanWholeEntries30284_7
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanEvenDomain30284_7)
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanWholeDomain30284_7)
  · simpa only [adaptiveSpanLevel30284, adaptiveSpanNumerator30284, adaptiveSpanDenominator30284, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 15142) (by decide : 0 < 899)
        adaptiveSpanProfilesValid30284 adaptiveOrder30284 adaptiveSpanNumericCheck30284_8
        adaptiveSpanEven30284_8 adaptiveSpanWhole30284_8
        adaptiveSpanEvenEntries30284_8 adaptiveSpanWholeEntries30284_8
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanEvenDomain30284_8)
        (by rw [adaptiveSpanProfileLength30284]; exact adaptiveSpanWholeDomain30284_8)

/-- The complete finite histogram certificate for 27531 ≤ n ≤ 30284. -/
theorem adaptiveSpanHistogram30284 : DegreeIntervalCertificate 30284 adaptiveSpanPrimes30284
    (fun s v => sharpDegree (27531 / 2) 8 (adaptiveSpanNumerator30284 s)
      (adaptiveSpanDenominator30284 s) (totientDensity v))
    (fun s v => sharpDegree 27531 8 (adaptiveSpanNumerator30284 s)
      (adaptiveSpanDenominator30284 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows30284)
    adaptiveSpanPrimes30284
    (fun s => sharpDegree (27531 / 2) 8 (adaptiveSpanNumerator30284 s) (adaptiveSpanDenominator30284 s))
    (fun s => sharpDegree 27531 8 (adaptiveSpanNumerator30284 s) (adaptiveSpanDenominator30284 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid30284 adaptiveOrder30284 adaptivePermutationSemantics30284
    (by rw [adaptiveSpanProfileLength30284]; decide +kernel)
    adaptiveSpanLevel30284 adaptiveSpanTreeCache30284 adaptiveSpanTreeRepresents30284
    (fun j => adaptiveSpanWitness30284.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength30284
  · exact adaptiveSpanWitnessCheck30284

/-- Every required odd cycle for a dense set, throughout 27531 ≤ n ≤ 30284. -/
theorem adaptiveSpanInterval30284 {n : ℕ} (hLn : 27531 ≤ n) (hnU : n ≤ 30284)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes30284
    adaptiveSpanNumerator30284 adaptiveSpanDenominator30284 adaptiveSpanSharpTail30284
    adaptiveSpanPrimeSupport30284 adaptiveSpanHistogram30284 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail30284
#print axioms adaptiveSpanPrimeSupport30284
#print axioms adaptiveSpanHistogram30284
#print axioms adaptiveSpanInterval30284
end Erdos883Verified
