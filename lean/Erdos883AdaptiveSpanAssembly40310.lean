import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate40310Metadata
import Erdos883AdaptiveSpan40310Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate40310PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes40310 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29]

def adaptiveSpanNumerator40310 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | 8 => 30240
  | _ => 1080

def adaptiveSpanDenominator40310 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | 8 => 33263
  | _ => 1147

theorem adaptiveSpanSharpTail40310 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes40310.length) :
    SharpTailCertificate 40310 (adaptiveSpanPrimes40310.take s)
      (adaptiveSpanNumerator40310 s) (adaptiveSpanDenominator40310 s) := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 40310 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 40310 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 40310 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 40310 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 40310 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 40310 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 40310 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 40310 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 40310 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 40310 [3, 5, 7, 11, 13, 17, 19, 23, 29] 1080 1147
    refine ⟨by decide, {31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport40310 : ∀ u ∈ oddUniverse 40310,
    ∀ v ∈ oddUniverse 40310, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid40310 : AdaptiveProfileRowsValid adaptiveRows40310 :=
  coreProfileMetadataCheck_sound adaptiveMetadata40310

theorem adaptiveSpanProfileLength40310 : adaptiveRows40310.length = halfOdds 40310 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics40310
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache40310 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes40310.length) :
    (adaptiveSpanLevel40310 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel40310 s).2.cacheCheck = true := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel40310, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache40310_0 adaptiveSpanWholeCache40310_0
  · simpa only [adaptiveSpanLevel40310, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache40310_1 adaptiveSpanWholeCache40310_1
  · simpa only [adaptiveSpanLevel40310, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache40310_2 adaptiveSpanWholeCache40310_2
  · simpa only [adaptiveSpanLevel40310, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache40310_3 adaptiveSpanWholeCache40310_3
  · simpa only [adaptiveSpanLevel40310, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache40310_4 adaptiveSpanWholeCache40310_4
  · simpa only [adaptiveSpanLevel40310, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache40310_5 adaptiveSpanWholeCache40310_5
  · simpa only [adaptiveSpanLevel40310, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache40310_6 adaptiveSpanWholeCache40310_6
  · simpa only [adaptiveSpanLevel40310, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache40310_7 adaptiveSpanWholeCache40310_7
  · simpa only [adaptiveSpanLevel40310, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache40310_8 adaptiveSpanWholeCache40310_8
  · simpa only [adaptiveSpanLevel40310, (show (9 : ℕ) ≠ 0 by decide), (show (9 : ℕ) ≠ 1 by decide), (show (9 : ℕ) ≠ 2 by decide), (show (9 : ℕ) ≠ 3 by decide), (show (9 : ℕ) ≠ 4 by decide), (show (9 : ℕ) ≠ 5 by decide), (show (9 : ℕ) ≠ 6 by decide), (show (9 : ℕ) ≠ 7 by decide), (show (9 : ℕ) ≠ 8 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache40310_9 adaptiveSpanWholeCache40310_9

theorem adaptiveSpanTreeRepresents40310 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes40310.length) :
    AdaptiveSpanTreeRepresents adaptiveRows40310 (halfOdds 40310)
      (sharpDegree (36646 / 2) 8 (adaptiveSpanNumerator40310 s) (adaptiveSpanDenominator40310 s))
      (sharpDegree 36646 8 (adaptiveSpanNumerator40310 s) (adaptiveSpanDenominator40310 s))
      (adaptiveSpanLevel40310 s).1 (adaptiveSpanLevel40310 s).2 := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel40310, adaptiveSpanNumerator40310, adaptiveSpanDenominator40310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 20155) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptiveSpanNumericCheck40310_0
        adaptiveSpanEven40310_0 adaptiveSpanWhole40310_0
        adaptiveSpanEvenEntries40310_0 adaptiveSpanWholeEntries40310_0
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanEvenDomain40310_0)
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanWholeDomain40310_0)
  · simpa only [adaptiveSpanLevel40310, adaptiveSpanNumerator40310, adaptiveSpanDenominator40310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 20155) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptiveSpanNumericCheck40310_1
        adaptiveSpanEven40310_1 adaptiveSpanWhole40310_1
        adaptiveSpanEvenEntries40310_1 adaptiveSpanWholeEntries40310_1
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanEvenDomain40310_1)
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanWholeDomain40310_1)
  · simpa only [adaptiveSpanLevel40310, adaptiveSpanNumerator40310, adaptiveSpanDenominator40310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 20155) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptiveSpanNumericCheck40310_2
        adaptiveSpanEven40310_2 adaptiveSpanWhole40310_2
        adaptiveSpanEvenEntries40310_2 adaptiveSpanWholeEntries40310_2
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanEvenDomain40310_2)
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanWholeDomain40310_2)
  · simpa only [adaptiveSpanLevel40310, adaptiveSpanNumerator40310, adaptiveSpanDenominator40310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 20155) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptiveSpanNumericCheck40310_3
        adaptiveSpanEven40310_3 adaptiveSpanWhole40310_3
        adaptiveSpanEvenEntries40310_3 adaptiveSpanWholeEntries40310_3
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanEvenDomain40310_3)
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanWholeDomain40310_3)
  · simpa only [adaptiveSpanLevel40310, adaptiveSpanNumerator40310, adaptiveSpanDenominator40310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 20155) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptiveSpanNumericCheck40310_4
        adaptiveSpanEven40310_4 adaptiveSpanWhole40310_4
        adaptiveSpanEvenEntries40310_4 adaptiveSpanWholeEntries40310_4
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanEvenDomain40310_4)
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanWholeDomain40310_4)
  · simpa only [adaptiveSpanLevel40310, adaptiveSpanNumerator40310, adaptiveSpanDenominator40310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 20155) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptiveSpanNumericCheck40310_5
        adaptiveSpanEven40310_5 adaptiveSpanWhole40310_5
        adaptiveSpanEvenEntries40310_5 adaptiveSpanWholeEntries40310_5
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanEvenDomain40310_5)
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanWholeDomain40310_5)
  · simpa only [adaptiveSpanLevel40310, adaptiveSpanNumerator40310, adaptiveSpanDenominator40310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 20155) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptiveSpanNumericCheck40310_6
        adaptiveSpanEven40310_6 adaptiveSpanWhole40310_6
        adaptiveSpanEvenEntries40310_6 adaptiveSpanWholeEntries40310_6
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanEvenDomain40310_6)
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanWholeDomain40310_6)
  · simpa only [adaptiveSpanLevel40310, adaptiveSpanNumerator40310, adaptiveSpanDenominator40310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 20155) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptiveSpanNumericCheck40310_7
        adaptiveSpanEven40310_7 adaptiveSpanWhole40310_7
        adaptiveSpanEvenEntries40310_7 adaptiveSpanWholeEntries40310_7
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanEvenDomain40310_7)
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanWholeDomain40310_7)
  · simpa only [adaptiveSpanLevel40310, adaptiveSpanNumerator40310, adaptiveSpanDenominator40310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 20155) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptiveSpanNumericCheck40310_8
        adaptiveSpanEven40310_8 adaptiveSpanWhole40310_8
        adaptiveSpanEvenEntries40310_8 adaptiveSpanWholeEntries40310_8
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanEvenDomain40310_8)
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanWholeDomain40310_8)
  · simpa only [adaptiveSpanLevel40310, adaptiveSpanNumerator40310, adaptiveSpanDenominator40310, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (9 : ℕ) ≠ 0 by decide), (show (9 : ℕ) ≠ 1 by decide), (show (9 : ℕ) ≠ 2 by decide), (show (9 : ℕ) ≠ 3 by decide), (show (9 : ℕ) ≠ 4 by decide), (show (9 : ℕ) ≠ 5 by decide), (show (9 : ℕ) ≠ 6 by decide), (show (9 : ℕ) ≠ 7 by decide), (show (9 : ℕ) ≠ 8 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 20155) (by decide : 0 < 1147)
        adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptiveSpanNumericCheck40310_9
        adaptiveSpanEven40310_9 adaptiveSpanWhole40310_9
        adaptiveSpanEvenEntries40310_9 adaptiveSpanWholeEntries40310_9
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanEvenDomain40310_9)
        (by rw [adaptiveSpanProfileLength40310]; exact adaptiveSpanWholeDomain40310_9)

/-- The complete finite histogram certificate for 36646 ≤ n ≤ 40310. -/
theorem adaptiveSpanHistogram40310 : DegreeIntervalCertificate 40310 adaptiveSpanPrimes40310
    (fun s v => sharpDegree (36646 / 2) 8 (adaptiveSpanNumerator40310 s)
      (adaptiveSpanDenominator40310 s) (totientDensity v))
    (fun s v => sharpDegree 36646 8 (adaptiveSpanNumerator40310 s)
      (adaptiveSpanDenominator40310 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows40310)
    adaptiveSpanPrimes40310
    (fun s => sharpDegree (36646 / 2) 8 (adaptiveSpanNumerator40310 s) (adaptiveSpanDenominator40310 s))
    (fun s => sharpDegree 36646 8 (adaptiveSpanNumerator40310 s) (adaptiveSpanDenominator40310 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid40310 adaptiveOrder40310 adaptivePermutationSemantics40310
    (by rw [adaptiveSpanProfileLength40310]; decide +kernel)
    adaptiveSpanLevel40310 adaptiveSpanTreeCache40310 adaptiveSpanTreeRepresents40310
    (fun j => adaptiveSpanWitness40310.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength40310
  · exact adaptiveSpanWitnessCheck40310

/-- Every required odd cycle for a dense set, throughout 36646 ≤ n ≤ 40310. -/
theorem adaptiveSpanInterval40310 {n : ℕ} (hLn : 36646 ≤ n) (hnU : n ≤ 40310)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes40310
    adaptiveSpanNumerator40310 adaptiveSpanDenominator40310 adaptiveSpanSharpTail40310
    adaptiveSpanPrimeSupport40310 adaptiveSpanHistogram40310 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail40310
#print axioms adaptiveSpanPrimeSupport40310
#print axioms adaptiveSpanHistogram40310
#print axioms adaptiveSpanInterval40310
end Erdos883Verified
