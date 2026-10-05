import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate4250Metadata
import Erdos883AdaptiveSpan4250Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes4250 : List ℕ := [3, 5, 7, 11, 13, 17]

def adaptiveSpanNumerator4250 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 288
  | _ => 396

def adaptiveSpanDenominator4250 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 323
  | _ => 437

theorem adaptiveSpanSharpTail4250 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4250.length) :
    SharpTailCertificate 4250 (adaptiveSpanPrimes4250.take s)
      (adaptiveSpanNumerator4250 s) (adaptiveSpanDenominator4250 s) := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 4250 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4250 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4250 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4250 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4250 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4250 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 4250 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport4250 : ∀ u ∈ oddUniverse 4250,
    ∀ v ∈ oddUniverse 4250, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid4250 : AdaptiveProfileRowsValid adaptiveRows4250 :=
  coreProfileMetadataCheck_sound adaptiveMetadata4250

theorem adaptiveSpanProfileLength4250 : adaptiveRows4250.length = halfOdds 4250 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation4250)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache4250 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4250.length) :
    (adaptiveSpanLevel4250 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel4250 s).2.cacheCheck = true := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel4250, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4250_0 adaptiveSpanWholeCache4250_0
  · simpa only [adaptiveSpanLevel4250, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4250_1 adaptiveSpanWholeCache4250_1
  · simpa only [adaptiveSpanLevel4250, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4250_2 adaptiveSpanWholeCache4250_2
  · simpa only [adaptiveSpanLevel4250, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4250_3 adaptiveSpanWholeCache4250_3
  · simpa only [adaptiveSpanLevel4250, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4250_4 adaptiveSpanWholeCache4250_4
  · simpa only [adaptiveSpanLevel4250, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4250_5 adaptiveSpanWholeCache4250_5
  · simpa only [adaptiveSpanLevel4250, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache4250_6 adaptiveSpanWholeCache4250_6

theorem adaptiveSpanTreeRepresents4250 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes4250.length) :
    AdaptiveSpanTreeRepresents adaptiveRows4250 (halfOdds 4250)
      (sharpDegree (4048 / 2) 7 (adaptiveSpanNumerator4250 s) (adaptiveSpanDenominator4250 s))
      (sharpDegree 4048 7 (adaptiveSpanNumerator4250 s) (adaptiveSpanDenominator4250 s))
      (adaptiveSpanLevel4250 s).1 (adaptiveSpanLevel4250 s).2 := by
  have hs' : s ≤ 6 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel4250, adaptiveSpanNumerator4250, adaptiveSpanDenominator4250, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2125) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid4250 adaptiveOrder4250 adaptiveSpanNumericCheck4250_0
        adaptiveSpanEven4250_0 adaptiveSpanWhole4250_0
        adaptiveSpanEvenEntries4250_0 adaptiveSpanWholeEntries4250_0
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanEvenDomain4250_0)
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanWholeDomain4250_0)
  · simpa only [adaptiveSpanLevel4250, adaptiveSpanNumerator4250, adaptiveSpanDenominator4250, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2125) (by decide : 0 < 385)
        adaptiveSpanProfilesValid4250 adaptiveOrder4250 adaptiveSpanNumericCheck4250_1
        adaptiveSpanEven4250_1 adaptiveSpanWhole4250_1
        adaptiveSpanEvenEntries4250_1 adaptiveSpanWholeEntries4250_1
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanEvenDomain4250_1)
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanWholeDomain4250_1)
  · simpa only [adaptiveSpanLevel4250, adaptiveSpanNumerator4250, adaptiveSpanDenominator4250, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2125) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid4250 adaptiveOrder4250 adaptiveSpanNumericCheck4250_2
        adaptiveSpanEven4250_2 adaptiveSpanWhole4250_2
        adaptiveSpanEvenEntries4250_2 adaptiveSpanWholeEntries4250_2
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanEvenDomain4250_2)
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanWholeDomain4250_2)
  · simpa only [adaptiveSpanLevel4250, adaptiveSpanNumerator4250, adaptiveSpanDenominator4250, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2125) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid4250 adaptiveOrder4250 adaptiveSpanNumericCheck4250_3
        adaptiveSpanEven4250_3 adaptiveSpanWhole4250_3
        adaptiveSpanEvenEntries4250_3 adaptiveSpanWholeEntries4250_3
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanEvenDomain4250_3)
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanWholeDomain4250_3)
  · simpa only [adaptiveSpanLevel4250, adaptiveSpanNumerator4250, adaptiveSpanDenominator4250, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2125) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid4250 adaptiveOrder4250 adaptiveSpanNumericCheck4250_4
        adaptiveSpanEven4250_4 adaptiveSpanWhole4250_4
        adaptiveSpanEvenEntries4250_4 adaptiveSpanWholeEntries4250_4
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanEvenDomain4250_4)
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanWholeDomain4250_4)
  · simpa only [adaptiveSpanLevel4250, adaptiveSpanNumerator4250, adaptiveSpanDenominator4250, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2125) (by decide : 0 < 323)
        adaptiveSpanProfilesValid4250 adaptiveOrder4250 adaptiveSpanNumericCheck4250_5
        adaptiveSpanEven4250_5 adaptiveSpanWhole4250_5
        adaptiveSpanEvenEntries4250_5 adaptiveSpanWholeEntries4250_5
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanEvenDomain4250_5)
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanWholeDomain4250_5)
  · simpa only [adaptiveSpanLevel4250, adaptiveSpanNumerator4250, adaptiveSpanDenominator4250, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 2125) (by decide : 0 < 437)
        adaptiveSpanProfilesValid4250 adaptiveOrder4250 adaptiveSpanNumericCheck4250_6
        adaptiveSpanEven4250_6 adaptiveSpanWhole4250_6
        adaptiveSpanEvenEntries4250_6 adaptiveSpanWholeEntries4250_6
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanEvenDomain4250_6)
        (by rw [adaptiveSpanProfileLength4250]; exact adaptiveSpanWholeDomain4250_6)

/-- The complete finite histogram certificate for 4048 ≤ n ≤ 4250. -/
theorem adaptiveSpanHistogram4250 : DegreeIntervalCertificate 4250 adaptiveSpanPrimes4250
    (fun s v => sharpDegree (4048 / 2) 7 (adaptiveSpanNumerator4250 s)
      (adaptiveSpanDenominator4250 s) (totientDensity v))
    (fun s v => sharpDegree 4048 7 (adaptiveSpanNumerator4250 s)
      (adaptiveSpanDenominator4250 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows4250)
    adaptiveSpanPrimes4250
    (fun s => sharpDegree (4048 / 2) 7 (adaptiveSpanNumerator4250 s) (adaptiveSpanDenominator4250 s))
    (fun s => sharpDegree 4048 7 (adaptiveSpanNumerator4250 s) (adaptiveSpanDenominator4250 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid4250 adaptiveOrder4250 (coreOrderPermutationCheck_sound adaptivePermutation4250)
    (by rw [adaptiveSpanProfileLength4250]; decide +kernel)
    adaptiveSpanLevel4250 adaptiveSpanTreeCache4250 adaptiveSpanTreeRepresents4250
    (fun j => adaptiveSpanWitness4250.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck4250

/-- Every required odd cycle for a dense set, throughout 4048 ≤ n ≤ 4250. -/
theorem adaptiveSpanInterval4250 {n : ℕ} (hLn : 4048 ≤ n) (hnU : n ≤ 4250)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes4250
    adaptiveSpanNumerator4250 adaptiveSpanDenominator4250 adaptiveSpanSharpTail4250
    adaptiveSpanPrimeSupport4250 adaptiveSpanHistogram4250 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail4250
#print axioms adaptiveSpanPrimeSupport4250
#print axioms adaptiveSpanHistogram4250
#print axioms adaptiveSpanInterval4250
end Erdos883Verified
