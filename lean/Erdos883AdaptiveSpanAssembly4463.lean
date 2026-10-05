import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate4463Metadata
import Erdos883AdaptiveSpan4463Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes4463 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator4463 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator4463 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail4463 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4463.length) :
    SharpTailCertificate 4463 (adaptiveSpanPrimes4463.take s)
      (adaptiveSpanNumerator4463 s) (adaptiveSpanDenominator4463 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 4463 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4463 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4463 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4463 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4463 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4463 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4463 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport4463 : ∀ u ∈ oddUniverse 4463,
    ∀ v ∈ oddUniverse 4463, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid4463 : AdaptiveProfileRowsValid adaptiveRows4463 :=
  coreProfileMetadataCheck_sound adaptiveMetadata4463

theorem adaptiveSpanProfileLength4463 : adaptiveRows4463.length = halfOdds 4463 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation4463)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache4463 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4463.length) :
    (adaptiveSpanLevel4463 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel4463 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel4463, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4463_0 adaptiveSpanWholeCache4463_0
  · simpa only [adaptiveSpanLevel4463, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4463_1 adaptiveSpanWholeCache4463_1
  · simpa only [adaptiveSpanLevel4463, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4463_2 adaptiveSpanWholeCache4463_2
  · simpa only [adaptiveSpanLevel4463, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4463_3 adaptiveSpanWholeCache4463_3
  · simpa only [adaptiveSpanLevel4463, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4463_4 adaptiveSpanWholeCache4463_4
  · simpa only [adaptiveSpanLevel4463, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4463_5 adaptiveSpanWholeCache4463_5
  · simpa only [adaptiveSpanLevel4463, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4463_6 adaptiveSpanWholeCache4463_6

theorem adaptiveSpanTreeRepresents4463 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4463.length) :
    AdaptiveSpanTreeRepresents adaptiveRows4463 (halfOdds 4463)
      (sharpDegree (4251 / 2) 7 (adaptiveSpanNumerator4463 s) (adaptiveSpanDenominator4463 s))
      (sharpDegree 4251 7 (adaptiveSpanNumerator4463 s) (adaptiveSpanDenominator4463 s))
      (adaptiveSpanLevel4463 s).1 (adaptiveSpanLevel4463 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel4463, adaptiveSpanNumerator4463, adaptiveSpanDenominator4463, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2232) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid4463 adaptiveOrder4463 adaptiveSpanNumericCheck4463_0
        adaptiveSpanEven4463_0 adaptiveSpanWhole4463_0
        adaptiveSpanEvenEntries4463_0 adaptiveSpanWholeEntries4463_0
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanEvenDomain4463_0)
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanWholeDomain4463_0)
  · simpa only [adaptiveSpanLevel4463, adaptiveSpanNumerator4463, adaptiveSpanDenominator4463, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2232) (by decide : 0 < 385)
        adaptiveSpanProfilesValid4463 adaptiveOrder4463 adaptiveSpanNumericCheck4463_1
        adaptiveSpanEven4463_1 adaptiveSpanWhole4463_1
        adaptiveSpanEvenEntries4463_1 adaptiveSpanWholeEntries4463_1
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanEvenDomain4463_1)
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanWholeDomain4463_1)
  · simpa only [adaptiveSpanLevel4463, adaptiveSpanNumerator4463, adaptiveSpanDenominator4463, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2232) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid4463 adaptiveOrder4463 adaptiveSpanNumericCheck4463_2
        adaptiveSpanEven4463_2 adaptiveSpanWhole4463_2
        adaptiveSpanEvenEntries4463_2 adaptiveSpanWholeEntries4463_2
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanEvenDomain4463_2)
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanWholeDomain4463_2)
  · simpa only [adaptiveSpanLevel4463, adaptiveSpanNumerator4463, adaptiveSpanDenominator4463, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2232) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid4463 adaptiveOrder4463 adaptiveSpanNumericCheck4463_3
        adaptiveSpanEven4463_3 adaptiveSpanWhole4463_3
        adaptiveSpanEvenEntries4463_3 adaptiveSpanWholeEntries4463_3
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanEvenDomain4463_3)
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanWholeDomain4463_3)
  · simpa only [adaptiveSpanLevel4463, adaptiveSpanNumerator4463, adaptiveSpanDenominator4463, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2232) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid4463 adaptiveOrder4463 adaptiveSpanNumericCheck4463_4
        adaptiveSpanEven4463_4 adaptiveSpanWhole4463_4
        adaptiveSpanEvenEntries4463_4 adaptiveSpanWholeEntries4463_4
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanEvenDomain4463_4)
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanWholeDomain4463_4)
  · simpa only [adaptiveSpanLevel4463, adaptiveSpanNumerator4463, adaptiveSpanDenominator4463, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2232) (by decide : 0 < 323)
        adaptiveSpanProfilesValid4463 adaptiveOrder4463 adaptiveSpanNumericCheck4463_5
        adaptiveSpanEven4463_5 adaptiveSpanWhole4463_5
        adaptiveSpanEvenEntries4463_5 adaptiveSpanWholeEntries4463_5
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanEvenDomain4463_5)
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanWholeDomain4463_5)
  · simpa only [adaptiveSpanLevel4463, adaptiveSpanNumerator4463, adaptiveSpanDenominator4463, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2232) (by decide : 0 < 437)
        adaptiveSpanProfilesValid4463 adaptiveOrder4463 adaptiveSpanNumericCheck4463_6
        adaptiveSpanEven4463_6 adaptiveSpanWhole4463_6
        adaptiveSpanEvenEntries4463_6 adaptiveSpanWholeEntries4463_6
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanEvenDomain4463_6)
        (by rw [adaptiveSpanProfileLength4463]; exact adaptiveSpanWholeDomain4463_6)

/-- The complete finite histogram certificate for 4251 ≤ n ≤ 4463. -/
theorem adaptiveSpanHistogram4463 : DegreeIntervalCertificate 4463 adaptiveSpanPrimes4463
    (fun s v => sharpDegree (4251 / 2) 7 (adaptiveSpanNumerator4463 s)
      (adaptiveSpanDenominator4463 s) (totientDensity v))
    (fun s v => sharpDegree 4251 7 (adaptiveSpanNumerator4463 s)
      (adaptiveSpanDenominator4463 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows4463)
    adaptiveSpanPrimes4463
    (fun s => sharpDegree (4251 / 2) 7 (adaptiveSpanNumerator4463 s) (adaptiveSpanDenominator4463 s))
    (fun s => sharpDegree 4251 7 (adaptiveSpanNumerator4463 s) (adaptiveSpanDenominator4463 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid4463 adaptiveOrder4463 (coreOrderPermutationCheck_sound adaptivePermutation4463)
    (by rw [adaptiveSpanProfileLength4463]; decide +kernel)
    adaptiveSpanLevel4463 adaptiveSpanTreeCache4463 adaptiveSpanTreeRepresents4463
    (fun j => adaptiveSpanWitness4463.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck4463

/-- Every required odd cycle for a dense set, throughout 4251 ≤ n ≤ 4463. -/
theorem adaptiveSpanInterval4463 {n : ℕ} (hLn : 4251 ≤ n) (hnU : n ≤ 4463)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes4463
    adaptiveSpanNumerator4463 adaptiveSpanDenominator4463 adaptiveSpanSharpTail4463
    adaptiveSpanPrimeSupport4463 adaptiveSpanHistogram4463 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail4463
#print axioms adaptiveSpanPrimeSupport4463
#print axioms adaptiveSpanHistogram4463
#print axioms adaptiveSpanInterval4463
end Erdos883Verified
