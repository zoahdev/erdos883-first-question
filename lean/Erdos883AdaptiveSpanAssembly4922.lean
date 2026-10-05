import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate4922Metadata
import Erdos883AdaptiveSpan4922Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes4922 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator4922 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator4922 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail4922 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4922.length) :
    SharpTailCertificate 4922 (adaptiveSpanPrimes4922.take s)
      (adaptiveSpanNumerator4922 s) (adaptiveSpanDenominator4922 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 4922 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4922 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4922 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4922 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4922 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4922 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4922 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport4922 : ∀ u ∈ oddUniverse 4922,
    ∀ v ∈ oddUniverse 4922, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid4922 : AdaptiveProfileRowsValid adaptiveRows4922 :=
  coreProfileMetadataCheck_sound adaptiveMetadata4922

theorem adaptiveSpanProfileLength4922 : adaptiveRows4922.length = halfOdds 4922 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation4922)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache4922 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4922.length) :
    (adaptiveSpanLevel4922 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel4922 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel4922, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4922_0 adaptiveSpanWholeCache4922_0
  · simpa only [adaptiveSpanLevel4922, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4922_1 adaptiveSpanWholeCache4922_1
  · simpa only [adaptiveSpanLevel4922, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4922_2 adaptiveSpanWholeCache4922_2
  · simpa only [adaptiveSpanLevel4922, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4922_3 adaptiveSpanWholeCache4922_3
  · simpa only [adaptiveSpanLevel4922, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4922_4 adaptiveSpanWholeCache4922_4
  · simpa only [adaptiveSpanLevel4922, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4922_5 adaptiveSpanWholeCache4922_5
  · simpa only [adaptiveSpanLevel4922, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4922_6 adaptiveSpanWholeCache4922_6

theorem adaptiveSpanTreeRepresents4922 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4922.length) :
    AdaptiveSpanTreeRepresents adaptiveRows4922 (halfOdds 4922)
      (sharpDegree (4688 / 2) 7 (adaptiveSpanNumerator4922 s) (adaptiveSpanDenominator4922 s))
      (sharpDegree 4688 7 (adaptiveSpanNumerator4922 s) (adaptiveSpanDenominator4922 s))
      (adaptiveSpanLevel4922 s).1 (adaptiveSpanLevel4922 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel4922, adaptiveSpanNumerator4922, adaptiveSpanDenominator4922, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2461) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid4922 adaptiveOrder4922 adaptiveSpanNumericCheck4922_0
        adaptiveSpanEven4922_0 adaptiveSpanWhole4922_0
        adaptiveSpanEvenEntries4922_0 adaptiveSpanWholeEntries4922_0
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanEvenDomain4922_0)
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanWholeDomain4922_0)
  · simpa only [adaptiveSpanLevel4922, adaptiveSpanNumerator4922, adaptiveSpanDenominator4922, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2461) (by decide : 0 < 385)
        adaptiveSpanProfilesValid4922 adaptiveOrder4922 adaptiveSpanNumericCheck4922_1
        adaptiveSpanEven4922_1 adaptiveSpanWhole4922_1
        adaptiveSpanEvenEntries4922_1 adaptiveSpanWholeEntries4922_1
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanEvenDomain4922_1)
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanWholeDomain4922_1)
  · simpa only [adaptiveSpanLevel4922, adaptiveSpanNumerator4922, adaptiveSpanDenominator4922, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2461) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid4922 adaptiveOrder4922 adaptiveSpanNumericCheck4922_2
        adaptiveSpanEven4922_2 adaptiveSpanWhole4922_2
        adaptiveSpanEvenEntries4922_2 adaptiveSpanWholeEntries4922_2
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanEvenDomain4922_2)
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanWholeDomain4922_2)
  · simpa only [adaptiveSpanLevel4922, adaptiveSpanNumerator4922, adaptiveSpanDenominator4922, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2461) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid4922 adaptiveOrder4922 adaptiveSpanNumericCheck4922_3
        adaptiveSpanEven4922_3 adaptiveSpanWhole4922_3
        adaptiveSpanEvenEntries4922_3 adaptiveSpanWholeEntries4922_3
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanEvenDomain4922_3)
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanWholeDomain4922_3)
  · simpa only [adaptiveSpanLevel4922, adaptiveSpanNumerator4922, adaptiveSpanDenominator4922, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2461) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid4922 adaptiveOrder4922 adaptiveSpanNumericCheck4922_4
        adaptiveSpanEven4922_4 adaptiveSpanWhole4922_4
        adaptiveSpanEvenEntries4922_4 adaptiveSpanWholeEntries4922_4
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanEvenDomain4922_4)
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanWholeDomain4922_4)
  · simpa only [adaptiveSpanLevel4922, adaptiveSpanNumerator4922, adaptiveSpanDenominator4922, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2461) (by decide : 0 < 323)
        adaptiveSpanProfilesValid4922 adaptiveOrder4922 adaptiveSpanNumericCheck4922_5
        adaptiveSpanEven4922_5 adaptiveSpanWhole4922_5
        adaptiveSpanEvenEntries4922_5 adaptiveSpanWholeEntries4922_5
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanEvenDomain4922_5)
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanWholeDomain4922_5)
  · simpa only [adaptiveSpanLevel4922, adaptiveSpanNumerator4922, adaptiveSpanDenominator4922, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2461) (by decide : 0 < 437)
        adaptiveSpanProfilesValid4922 adaptiveOrder4922 adaptiveSpanNumericCheck4922_6
        adaptiveSpanEven4922_6 adaptiveSpanWhole4922_6
        adaptiveSpanEvenEntries4922_6 adaptiveSpanWholeEntries4922_6
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanEvenDomain4922_6)
        (by rw [adaptiveSpanProfileLength4922]; exact adaptiveSpanWholeDomain4922_6)

/-- The complete finite histogram certificate for 4688 ≤ n ≤ 4922. -/
theorem adaptiveSpanHistogram4922 : DegreeIntervalCertificate 4922 adaptiveSpanPrimes4922
    (fun s v => sharpDegree (4688 / 2) 7 (adaptiveSpanNumerator4922 s)
      (adaptiveSpanDenominator4922 s) (totientDensity v))
    (fun s v => sharpDegree 4688 7 (adaptiveSpanNumerator4922 s)
      (adaptiveSpanDenominator4922 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows4922)
    adaptiveSpanPrimes4922
    (fun s => sharpDegree (4688 / 2) 7 (adaptiveSpanNumerator4922 s) (adaptiveSpanDenominator4922 s))
    (fun s => sharpDegree 4688 7 (adaptiveSpanNumerator4922 s) (adaptiveSpanDenominator4922 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid4922 adaptiveOrder4922 (coreOrderPermutationCheck_sound adaptivePermutation4922)
    (by rw [adaptiveSpanProfileLength4922]; decide +kernel)
    adaptiveSpanLevel4922 adaptiveSpanTreeCache4922 adaptiveSpanTreeRepresents4922
    (fun j => adaptiveSpanWitness4922.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck4922

/-- Every required odd cycle for a dense set, throughout 4688 ≤ n ≤ 4922. -/
theorem adaptiveSpanInterval4922 {n : ℕ} (hLn : 4688 ≤ n) (hnU : n ≤ 4922)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes4922
    adaptiveSpanNumerator4922 adaptiveSpanDenominator4922 adaptiveSpanSharpTail4922
    adaptiveSpanPrimeSupport4922 adaptiveSpanHistogram4922 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail4922
#print axioms adaptiveSpanPrimeSupport4922
#print axioms adaptiveSpanHistogram4922
#print axioms adaptiveSpanInterval4922
end Erdos883Verified
