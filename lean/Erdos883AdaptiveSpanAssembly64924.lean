import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate64924Metadata
import Erdos883AdaptiveSpan64924Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate64924PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes64924 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator64924 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 34560
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator64924 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 46189
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail64924 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes64924.length) :
    SharpTailCertificate 64924 (adaptiveSpanPrimes64924.take s)
      (adaptiveSpanNumerator64924 s) (adaptiveSpanDenominator64924 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 64924 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 64924 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 64924 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 64924 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 64924 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 64924 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 64924 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 64924 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 64924 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport64924 : ∀ u ∈ oddUniverse 64924,
    ∀ v ∈ oddUniverse 64924, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid64924 : AdaptiveProfileRowsValid adaptiveRows64924 :=
  coreProfileMetadataCheck_sound adaptiveMetadata64924

theorem adaptiveSpanProfileLength64924 : adaptiveRows64924.length = halfOdds 64924 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics64924
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache64924 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes64924.length) :
    (adaptiveSpanLevel64924 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel64924 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel64924, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache64924_0 adaptiveSpanWholeCache64924_0
  · simpa only [adaptiveSpanLevel64924, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache64924_1 adaptiveSpanWholeCache64924_1
  · simpa only [adaptiveSpanLevel64924, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache64924_2 adaptiveSpanWholeCache64924_2
  · simpa only [adaptiveSpanLevel64924, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache64924_3 adaptiveSpanWholeCache64924_3
  · simpa only [adaptiveSpanLevel64924, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache64924_4 adaptiveSpanWholeCache64924_4
  · simpa only [adaptiveSpanLevel64924, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache64924_5 adaptiveSpanWholeCache64924_5
  · simpa only [adaptiveSpanLevel64924, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache64924_6 adaptiveSpanWholeCache64924_6
  · simpa only [adaptiveSpanLevel64924, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache64924_7 adaptiveSpanWholeCache64924_7
  · simpa only [adaptiveSpanLevel64924, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache64924_8 adaptiveSpanWholeCache64924_8

theorem adaptiveSpanTreeRepresents64924 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes64924.length) :
    AdaptiveSpanTreeRepresents adaptiveRows64924 (halfOdds 64924)
      (sharpDegree (59022 / 2) 9 (adaptiveSpanNumerator64924 s) (adaptiveSpanDenominator64924 s))
      (sharpDegree 59022 9 (adaptiveSpanNumerator64924 s) (adaptiveSpanDenominator64924 s))
      (adaptiveSpanLevel64924 s).1 (adaptiveSpanLevel64924 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel64924, adaptiveSpanNumerator64924, adaptiveSpanDenominator64924, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 32462) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid64924 adaptiveOrder64924 adaptiveSpanNumericCheck64924_0
        adaptiveSpanEven64924_0 adaptiveSpanWhole64924_0
        adaptiveSpanEvenEntries64924_0 adaptiveSpanWholeEntries64924_0
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanEvenDomain64924_0)
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanWholeDomain64924_0)
  · simpa only [adaptiveSpanLevel64924, adaptiveSpanNumerator64924, adaptiveSpanDenominator64924, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 32462) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid64924 adaptiveOrder64924 adaptiveSpanNumericCheck64924_1
        adaptiveSpanEven64924_1 adaptiveSpanWhole64924_1
        adaptiveSpanEvenEntries64924_1 adaptiveSpanWholeEntries64924_1
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanEvenDomain64924_1)
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanWholeDomain64924_1)
  · simpa only [adaptiveSpanLevel64924, adaptiveSpanNumerator64924, adaptiveSpanDenominator64924, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 32462) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid64924 adaptiveOrder64924 adaptiveSpanNumericCheck64924_2
        adaptiveSpanEven64924_2 adaptiveSpanWhole64924_2
        adaptiveSpanEvenEntries64924_2 adaptiveSpanWholeEntries64924_2
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanEvenDomain64924_2)
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanWholeDomain64924_2)
  · simpa only [adaptiveSpanLevel64924, adaptiveSpanNumerator64924, adaptiveSpanDenominator64924, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 32462) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid64924 adaptiveOrder64924 adaptiveSpanNumericCheck64924_3
        adaptiveSpanEven64924_3 adaptiveSpanWhole64924_3
        adaptiveSpanEvenEntries64924_3 adaptiveSpanWholeEntries64924_3
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanEvenDomain64924_3)
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanWholeDomain64924_3)
  · simpa only [adaptiveSpanLevel64924, adaptiveSpanNumerator64924, adaptiveSpanDenominator64924, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 32462) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid64924 adaptiveOrder64924 adaptiveSpanNumericCheck64924_4
        adaptiveSpanEven64924_4 adaptiveSpanWhole64924_4
        adaptiveSpanEvenEntries64924_4 adaptiveSpanWholeEntries64924_4
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanEvenDomain64924_4)
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanWholeDomain64924_4)
  · simpa only [adaptiveSpanLevel64924, adaptiveSpanNumerator64924, adaptiveSpanDenominator64924, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 32462) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid64924 adaptiveOrder64924 adaptiveSpanNumericCheck64924_5
        adaptiveSpanEven64924_5 adaptiveSpanWhole64924_5
        adaptiveSpanEvenEntries64924_5 adaptiveSpanWholeEntries64924_5
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanEvenDomain64924_5)
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanWholeDomain64924_5)
  · simpa only [adaptiveSpanLevel64924, adaptiveSpanNumerator64924, adaptiveSpanDenominator64924, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 32462) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid64924 adaptiveOrder64924 adaptiveSpanNumericCheck64924_6
        adaptiveSpanEven64924_6 adaptiveSpanWhole64924_6
        adaptiveSpanEvenEntries64924_6 adaptiveSpanWholeEntries64924_6
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanEvenDomain64924_6)
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanWholeDomain64924_6)
  · simpa only [adaptiveSpanLevel64924, adaptiveSpanNumerator64924, adaptiveSpanDenominator64924, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 32462) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid64924 adaptiveOrder64924 adaptiveSpanNumericCheck64924_7
        adaptiveSpanEven64924_7 adaptiveSpanWhole64924_7
        adaptiveSpanEvenEntries64924_7 adaptiveSpanWholeEntries64924_7
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanEvenDomain64924_7)
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanWholeDomain64924_7)
  · simpa only [adaptiveSpanLevel64924, adaptiveSpanNumerator64924, adaptiveSpanDenominator64924, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 32462) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid64924 adaptiveOrder64924 adaptiveSpanNumericCheck64924_8
        adaptiveSpanEven64924_8 adaptiveSpanWhole64924_8
        adaptiveSpanEvenEntries64924_8 adaptiveSpanWholeEntries64924_8
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanEvenDomain64924_8)
        (by rw [adaptiveSpanProfileLength64924]; exact adaptiveSpanWholeDomain64924_8)

/-- The complete finite histogram certificate for 59022 ≤ n ≤ 64924. -/
theorem adaptiveSpanHistogram64924 : DegreeIntervalCertificate 64924 adaptiveSpanPrimes64924
    (fun s v => sharpDegree (59022 / 2) 9 (adaptiveSpanNumerator64924 s)
      (adaptiveSpanDenominator64924 s) (totientDensity v))
    (fun s v => sharpDegree 59022 9 (adaptiveSpanNumerator64924 s)
      (adaptiveSpanDenominator64924 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows64924)
    adaptiveSpanPrimes64924
    (fun s => sharpDegree (59022 / 2) 9 (adaptiveSpanNumerator64924 s) (adaptiveSpanDenominator64924 s))
    (fun s => sharpDegree 59022 9 (adaptiveSpanNumerator64924 s) (adaptiveSpanDenominator64924 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid64924 adaptiveOrder64924 adaptivePermutationSemantics64924
    (by rw [adaptiveSpanProfileLength64924]; decide +kernel)
    adaptiveSpanLevel64924 adaptiveSpanTreeCache64924 adaptiveSpanTreeRepresents64924
    (fun j => adaptiveSpanWitness64924.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength64924
  · exact adaptiveSpanWitnessCheck64924

/-- Every required odd cycle for a dense set, throughout 59022 ≤ n ≤ 64924. -/
theorem adaptiveSpanInterval64924 {n : ℕ} (hLn : 59022 ≤ n) (hnU : n ≤ 64924)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes64924
    adaptiveSpanNumerator64924 adaptiveSpanDenominator64924 adaptiveSpanSharpTail64924
    adaptiveSpanPrimeSupport64924 adaptiveSpanHistogram64924 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail64924
#print axioms adaptiveSpanPrimeSupport64924
#print axioms adaptiveSpanHistogram64924
#print axioms adaptiveSpanInterval64924
end Erdos883Verified
