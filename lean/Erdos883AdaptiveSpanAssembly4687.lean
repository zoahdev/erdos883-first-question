import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate4687Metadata
import Erdos883AdaptiveSpan4687Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes4687 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator4687 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator4687 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail4687 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4687.length) :
    SharpTailCertificate 4687 (adaptiveSpanPrimes4687.take s)
      (adaptiveSpanNumerator4687 s) (adaptiveSpanDenominator4687 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 4687 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4687 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4687 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4687 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4687 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4687 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4687 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport4687 : ∀ u ∈ oddUniverse 4687,
    ∀ v ∈ oddUniverse 4687, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid4687 : AdaptiveProfileRowsValid adaptiveRows4687 :=
  coreProfileMetadataCheck_sound adaptiveMetadata4687

theorem adaptiveSpanProfileLength4687 : adaptiveRows4687.length = halfOdds 4687 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation4687)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache4687 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4687.length) :
    (adaptiveSpanLevel4687 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel4687 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel4687, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4687_0 adaptiveSpanWholeCache4687_0
  · simpa only [adaptiveSpanLevel4687, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4687_1 adaptiveSpanWholeCache4687_1
  · simpa only [adaptiveSpanLevel4687, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4687_2 adaptiveSpanWholeCache4687_2
  · simpa only [adaptiveSpanLevel4687, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4687_3 adaptiveSpanWholeCache4687_3
  · simpa only [adaptiveSpanLevel4687, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4687_4 adaptiveSpanWholeCache4687_4
  · simpa only [adaptiveSpanLevel4687, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4687_5 adaptiveSpanWholeCache4687_5
  · simpa only [adaptiveSpanLevel4687, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4687_6 adaptiveSpanWholeCache4687_6

theorem adaptiveSpanTreeRepresents4687 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4687.length) :
    AdaptiveSpanTreeRepresents adaptiveRows4687 (halfOdds 4687)
      (sharpDegree (4464 / 2) 7 (adaptiveSpanNumerator4687 s) (adaptiveSpanDenominator4687 s))
      (sharpDegree 4464 7 (adaptiveSpanNumerator4687 s) (adaptiveSpanDenominator4687 s))
      (adaptiveSpanLevel4687 s).1 (adaptiveSpanLevel4687 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel4687, adaptiveSpanNumerator4687, adaptiveSpanDenominator4687, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2344) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid4687 adaptiveOrder4687 adaptiveSpanNumericCheck4687_0
        adaptiveSpanEven4687_0 adaptiveSpanWhole4687_0
        adaptiveSpanEvenEntries4687_0 adaptiveSpanWholeEntries4687_0
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanEvenDomain4687_0)
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanWholeDomain4687_0)
  · simpa only [adaptiveSpanLevel4687, adaptiveSpanNumerator4687, adaptiveSpanDenominator4687, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2344) (by decide : 0 < 385)
        adaptiveSpanProfilesValid4687 adaptiveOrder4687 adaptiveSpanNumericCheck4687_1
        adaptiveSpanEven4687_1 adaptiveSpanWhole4687_1
        adaptiveSpanEvenEntries4687_1 adaptiveSpanWholeEntries4687_1
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanEvenDomain4687_1)
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanWholeDomain4687_1)
  · simpa only [adaptiveSpanLevel4687, adaptiveSpanNumerator4687, adaptiveSpanDenominator4687, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2344) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid4687 adaptiveOrder4687 adaptiveSpanNumericCheck4687_2
        adaptiveSpanEven4687_2 adaptiveSpanWhole4687_2
        adaptiveSpanEvenEntries4687_2 adaptiveSpanWholeEntries4687_2
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanEvenDomain4687_2)
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanWholeDomain4687_2)
  · simpa only [adaptiveSpanLevel4687, adaptiveSpanNumerator4687, adaptiveSpanDenominator4687, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2344) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid4687 adaptiveOrder4687 adaptiveSpanNumericCheck4687_3
        adaptiveSpanEven4687_3 adaptiveSpanWhole4687_3
        adaptiveSpanEvenEntries4687_3 adaptiveSpanWholeEntries4687_3
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanEvenDomain4687_3)
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanWholeDomain4687_3)
  · simpa only [adaptiveSpanLevel4687, adaptiveSpanNumerator4687, adaptiveSpanDenominator4687, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2344) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid4687 adaptiveOrder4687 adaptiveSpanNumericCheck4687_4
        adaptiveSpanEven4687_4 adaptiveSpanWhole4687_4
        adaptiveSpanEvenEntries4687_4 adaptiveSpanWholeEntries4687_4
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanEvenDomain4687_4)
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanWholeDomain4687_4)
  · simpa only [adaptiveSpanLevel4687, adaptiveSpanNumerator4687, adaptiveSpanDenominator4687, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2344) (by decide : 0 < 323)
        adaptiveSpanProfilesValid4687 adaptiveOrder4687 adaptiveSpanNumericCheck4687_5
        adaptiveSpanEven4687_5 adaptiveSpanWhole4687_5
        adaptiveSpanEvenEntries4687_5 adaptiveSpanWholeEntries4687_5
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanEvenDomain4687_5)
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanWholeDomain4687_5)
  · simpa only [adaptiveSpanLevel4687, adaptiveSpanNumerator4687, adaptiveSpanDenominator4687, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2344) (by decide : 0 < 437)
        adaptiveSpanProfilesValid4687 adaptiveOrder4687 adaptiveSpanNumericCheck4687_6
        adaptiveSpanEven4687_6 adaptiveSpanWhole4687_6
        adaptiveSpanEvenEntries4687_6 adaptiveSpanWholeEntries4687_6
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanEvenDomain4687_6)
        (by rw [adaptiveSpanProfileLength4687]; exact adaptiveSpanWholeDomain4687_6)

/-- The complete finite histogram certificate for 4464 ≤ n ≤ 4687. -/
theorem adaptiveSpanHistogram4687 : DegreeIntervalCertificate 4687 adaptiveSpanPrimes4687
    (fun s v => sharpDegree (4464 / 2) 7 (adaptiveSpanNumerator4687 s)
      (adaptiveSpanDenominator4687 s) (totientDensity v))
    (fun s v => sharpDegree 4464 7 (adaptiveSpanNumerator4687 s)
      (adaptiveSpanDenominator4687 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows4687)
    adaptiveSpanPrimes4687
    (fun s => sharpDegree (4464 / 2) 7 (adaptiveSpanNumerator4687 s) (adaptiveSpanDenominator4687 s))
    (fun s => sharpDegree 4464 7 (adaptiveSpanNumerator4687 s) (adaptiveSpanDenominator4687 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid4687 adaptiveOrder4687 (coreOrderPermutationCheck_sound adaptivePermutation4687)
    (by rw [adaptiveSpanProfileLength4687]; decide +kernel)
    adaptiveSpanLevel4687 adaptiveSpanTreeCache4687 adaptiveSpanTreeRepresents4687
    (fun j => adaptiveSpanWitness4687.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck4687

/-- Every required odd cycle for a dense set, throughout 4464 ≤ n ≤ 4687. -/
theorem adaptiveSpanInterval4687 {n : ℕ} (hLn : 4464 ≤ n) (hnU : n ≤ 4687)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes4687
    adaptiveSpanNumerator4687 adaptiveSpanDenominator4687 adaptiveSpanSharpTail4687
    adaptiveSpanPrimeSupport4687 adaptiveSpanHistogram4687 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail4687
#print axioms adaptiveSpanPrimeSupport4687
#print axioms adaptiveSpanHistogram4687
#print axioms adaptiveSpanInterval4687
end Erdos883Verified
