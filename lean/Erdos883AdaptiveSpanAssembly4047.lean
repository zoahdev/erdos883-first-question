import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate4047Metadata
import Erdos883AdaptiveSpan4047Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes4047 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator4047 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 192
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator4047 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 221
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail4047 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4047.length) :
    SharpTailCertificate 4047 (adaptiveSpanPrimes4047.take s)
      (adaptiveSpanNumerator4047 s) (adaptiveSpanDenominator4047 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 4047 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4047 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4047 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4047 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4047 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4047 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4047 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport4047 : ∀ u ∈ oddUniverse 4047,
    ∀ v ∈ oddUniverse 4047, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid4047 : AdaptiveProfileRowsValid adaptiveRows4047 :=
  coreProfileMetadataCheck_sound adaptiveMetadata4047

theorem adaptiveSpanProfileLength4047 : adaptiveRows4047.length = halfOdds 4047 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation4047)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache4047 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4047.length) :
    (adaptiveSpanLevel4047 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel4047 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel4047, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4047_0 adaptiveSpanWholeCache4047_0
  · simpa only [adaptiveSpanLevel4047, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4047_1 adaptiveSpanWholeCache4047_1
  · simpa only [adaptiveSpanLevel4047, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4047_2 adaptiveSpanWholeCache4047_2
  · simpa only [adaptiveSpanLevel4047, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4047_3 adaptiveSpanWholeCache4047_3
  · simpa only [adaptiveSpanLevel4047, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4047_4 adaptiveSpanWholeCache4047_4
  · simpa only [adaptiveSpanLevel4047, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4047_5 adaptiveSpanWholeCache4047_5
  · simpa only [adaptiveSpanLevel4047, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4047_6 adaptiveSpanWholeCache4047_6

theorem adaptiveSpanTreeRepresents4047 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4047.length) :
    AdaptiveSpanTreeRepresents adaptiveRows4047 (halfOdds 4047)
      (sharpDegree (3855 / 2) 7 (adaptiveSpanNumerator4047 s) (adaptiveSpanDenominator4047 s))
      (sharpDegree 3855 7 (adaptiveSpanNumerator4047 s) (adaptiveSpanDenominator4047 s))
      (adaptiveSpanLevel4047 s).1 (adaptiveSpanLevel4047 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel4047, adaptiveSpanNumerator4047, adaptiveSpanDenominator4047, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2024) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid4047 adaptiveOrder4047 adaptiveSpanNumericCheck4047_0
        adaptiveSpanEven4047_0 adaptiveSpanWhole4047_0
        adaptiveSpanEvenEntries4047_0 adaptiveSpanWholeEntries4047_0
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanEvenDomain4047_0)
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanWholeDomain4047_0)
  · simpa only [adaptiveSpanLevel4047, adaptiveSpanNumerator4047, adaptiveSpanDenominator4047, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2024) (by decide : 0 < 385)
        adaptiveSpanProfilesValid4047 adaptiveOrder4047 adaptiveSpanNumericCheck4047_1
        adaptiveSpanEven4047_1 adaptiveSpanWhole4047_1
        adaptiveSpanEvenEntries4047_1 adaptiveSpanWholeEntries4047_1
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanEvenDomain4047_1)
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanWholeDomain4047_1)
  · simpa only [adaptiveSpanLevel4047, adaptiveSpanNumerator4047, adaptiveSpanDenominator4047, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2024) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid4047 adaptiveOrder4047 adaptiveSpanNumericCheck4047_2
        adaptiveSpanEven4047_2 adaptiveSpanWhole4047_2
        adaptiveSpanEvenEntries4047_2 adaptiveSpanWholeEntries4047_2
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanEvenDomain4047_2)
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanWholeDomain4047_2)
  · simpa only [adaptiveSpanLevel4047, adaptiveSpanNumerator4047, adaptiveSpanDenominator4047, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2024) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid4047 adaptiveOrder4047 adaptiveSpanNumericCheck4047_3
        adaptiveSpanEven4047_3 adaptiveSpanWhole4047_3
        adaptiveSpanEvenEntries4047_3 adaptiveSpanWholeEntries4047_3
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanEvenDomain4047_3)
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanWholeDomain4047_3)
  · simpa only [adaptiveSpanLevel4047, adaptiveSpanNumerator4047, adaptiveSpanDenominator4047, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2024) (by decide : 0 < 221)
        adaptiveSpanProfilesValid4047 adaptiveOrder4047 adaptiveSpanNumericCheck4047_4
        adaptiveSpanEven4047_4 adaptiveSpanWhole4047_4
        adaptiveSpanEvenEntries4047_4 adaptiveSpanWholeEntries4047_4
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanEvenDomain4047_4)
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanWholeDomain4047_4)
  · simpa only [adaptiveSpanLevel4047, adaptiveSpanNumerator4047, adaptiveSpanDenominator4047, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2024) (by decide : 0 < 323)
        adaptiveSpanProfilesValid4047 adaptiveOrder4047 adaptiveSpanNumericCheck4047_5
        adaptiveSpanEven4047_5 adaptiveSpanWhole4047_5
        adaptiveSpanEvenEntries4047_5 adaptiveSpanWholeEntries4047_5
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanEvenDomain4047_5)
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanWholeDomain4047_5)
  · simpa only [adaptiveSpanLevel4047, adaptiveSpanNumerator4047, adaptiveSpanDenominator4047, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2024) (by decide : 0 < 437)
        adaptiveSpanProfilesValid4047 adaptiveOrder4047 adaptiveSpanNumericCheck4047_6
        adaptiveSpanEven4047_6 adaptiveSpanWhole4047_6
        adaptiveSpanEvenEntries4047_6 adaptiveSpanWholeEntries4047_6
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanEvenDomain4047_6)
        (by rw [adaptiveSpanProfileLength4047]; exact adaptiveSpanWholeDomain4047_6)

/-- The complete finite histogram certificate for 3855 ≤ n ≤ 4047. -/
theorem adaptiveSpanHistogram4047 : DegreeIntervalCertificate 4047 adaptiveSpanPrimes4047
    (fun s v => sharpDegree (3855 / 2) 7 (adaptiveSpanNumerator4047 s)
      (adaptiveSpanDenominator4047 s) (totientDensity v))
    (fun s v => sharpDegree 3855 7 (adaptiveSpanNumerator4047 s)
      (adaptiveSpanDenominator4047 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows4047)
    adaptiveSpanPrimes4047
    (fun s => sharpDegree (3855 / 2) 7 (adaptiveSpanNumerator4047 s) (adaptiveSpanDenominator4047 s))
    (fun s => sharpDegree 3855 7 (adaptiveSpanNumerator4047 s) (adaptiveSpanDenominator4047 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid4047 adaptiveOrder4047 (coreOrderPermutationCheck_sound adaptivePermutation4047)
    (by rw [adaptiveSpanProfileLength4047]; decide +kernel)
    adaptiveSpanLevel4047 adaptiveSpanTreeCache4047 adaptiveSpanTreeRepresents4047
    (fun j => adaptiveSpanWitness4047.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck4047

/-- Every required odd cycle for a dense set, throughout 3855 ≤ n ≤ 4047. -/
theorem adaptiveSpanInterval4047 {n : ℕ} (hLn : 3855 ≤ n) (hnU : n ≤ 4047)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes4047
    adaptiveSpanNumerator4047 adaptiveSpanDenominator4047 adaptiveSpanSharpTail4047
    adaptiveSpanPrimeSupport4047 adaptiveSpanHistogram4047 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail4047
#print axioms adaptiveSpanPrimeSupport4047
#print axioms adaptiveSpanHistogram4047
#print axioms adaptiveSpanInterval4047
end Erdos883Verified
