import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate9644Metadata
import Erdos883AdaptiveSpan9644Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes9644 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator9644 : ℕ → ℕ
  | 0 => 480
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 396
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator9644 : ℕ → ℕ
  | 0 => 1155
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 437
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail9644 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes9644.length) :
    SharpTailCertificate 9644 (adaptiveSpanPrimes9644.take s)
      (adaptiveSpanNumerator9644 s) (adaptiveSpanDenominator9644 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 9644 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 9644 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 9644 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 9644 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 9644 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 9644 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 9644 [3, 5, 7, 11, 13, 17] 396 437
    refine ⟨by decide, {19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 9644 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 9644 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport9644 : ∀ u ∈ oddUniverse 9644,
    ∀ v ∈ oddUniverse 9644, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid9644 : AdaptiveProfileRowsValid adaptiveRows9644 :=
  coreProfileMetadataCheck_sound adaptiveMetadata9644

theorem adaptiveSpanProfileLength9644 : adaptiveRows9644.length = halfOdds 9644 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation9644)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache9644 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes9644.length) :
    (adaptiveSpanLevel9644 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel9644 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel9644, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache9644_0 adaptiveSpanWholeCache9644_0
  · simpa only [adaptiveSpanLevel9644, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache9644_1 adaptiveSpanWholeCache9644_1
  · simpa only [adaptiveSpanLevel9644, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache9644_2 adaptiveSpanWholeCache9644_2
  · simpa only [adaptiveSpanLevel9644, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache9644_3 adaptiveSpanWholeCache9644_3
  · simpa only [adaptiveSpanLevel9644, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache9644_4 adaptiveSpanWholeCache9644_4
  · simpa only [adaptiveSpanLevel9644, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache9644_5 adaptiveSpanWholeCache9644_5
  · simpa only [adaptiveSpanLevel9644, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache9644_6 adaptiveSpanWholeCache9644_6
  · simpa only [adaptiveSpanLevel9644, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache9644_7 adaptiveSpanWholeCache9644_7
  · simpa only [adaptiveSpanLevel9644, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache9644_8 adaptiveSpanWholeCache9644_8

theorem adaptiveSpanTreeRepresents9644 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes9644.length) :
    AdaptiveSpanTreeRepresents adaptiveRows9644 (halfOdds 9644)
      (sharpDegree (8768 / 2) 7 (adaptiveSpanNumerator9644 s) (adaptiveSpanDenominator9644 s))
      (sharpDegree 8768 7 (adaptiveSpanNumerator9644 s) (adaptiveSpanDenominator9644 s))
      (adaptiveSpanLevel9644 s).1 (adaptiveSpanLevel9644 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel9644, adaptiveSpanNumerator9644, adaptiveSpanDenominator9644, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4822) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid9644 adaptiveOrder9644 adaptiveSpanNumericCheck9644_0
        adaptiveSpanEven9644_0 adaptiveSpanWhole9644_0
        adaptiveSpanEvenEntries9644_0 adaptiveSpanWholeEntries9644_0
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanEvenDomain9644_0)
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanWholeDomain9644_0)
  · simpa only [adaptiveSpanLevel9644, adaptiveSpanNumerator9644, adaptiveSpanDenominator9644, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4822) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid9644 adaptiveOrder9644 adaptiveSpanNumericCheck9644_1
        adaptiveSpanEven9644_1 adaptiveSpanWhole9644_1
        adaptiveSpanEvenEntries9644_1 adaptiveSpanWholeEntries9644_1
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanEvenDomain9644_1)
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanWholeDomain9644_1)
  · simpa only [adaptiveSpanLevel9644, adaptiveSpanNumerator9644, adaptiveSpanDenominator9644, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4822) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid9644 adaptiveOrder9644 adaptiveSpanNumericCheck9644_2
        adaptiveSpanEven9644_2 adaptiveSpanWhole9644_2
        adaptiveSpanEvenEntries9644_2 adaptiveSpanWholeEntries9644_2
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanEvenDomain9644_2)
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanWholeDomain9644_2)
  · simpa only [adaptiveSpanLevel9644, adaptiveSpanNumerator9644, adaptiveSpanDenominator9644, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4822) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid9644 adaptiveOrder9644 adaptiveSpanNumericCheck9644_3
        adaptiveSpanEven9644_3 adaptiveSpanWhole9644_3
        adaptiveSpanEvenEntries9644_3 adaptiveSpanWholeEntries9644_3
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanEvenDomain9644_3)
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanWholeDomain9644_3)
  · simpa only [adaptiveSpanLevel9644, adaptiveSpanNumerator9644, adaptiveSpanDenominator9644, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4822) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid9644 adaptiveOrder9644 adaptiveSpanNumericCheck9644_4
        adaptiveSpanEven9644_4 adaptiveSpanWhole9644_4
        adaptiveSpanEvenEntries9644_4 adaptiveSpanWholeEntries9644_4
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanEvenDomain9644_4)
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanWholeDomain9644_4)
  · simpa only [adaptiveSpanLevel9644, adaptiveSpanNumerator9644, adaptiveSpanDenominator9644, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4822) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid9644 adaptiveOrder9644 adaptiveSpanNumericCheck9644_5
        adaptiveSpanEven9644_5 adaptiveSpanWhole9644_5
        adaptiveSpanEvenEntries9644_5 adaptiveSpanWholeEntries9644_5
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanEvenDomain9644_5)
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanWholeDomain9644_5)
  · simpa only [adaptiveSpanLevel9644, adaptiveSpanNumerator9644, adaptiveSpanDenominator9644, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4822) (by decide : 0 < 437)
        adaptiveSpanProfilesValid9644 adaptiveOrder9644 adaptiveSpanNumericCheck9644_6
        adaptiveSpanEven9644_6 adaptiveSpanWhole9644_6
        adaptiveSpanEvenEntries9644_6 adaptiveSpanWholeEntries9644_6
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanEvenDomain9644_6)
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanWholeDomain9644_6)
  · simpa only [adaptiveSpanLevel9644, adaptiveSpanNumerator9644, adaptiveSpanDenominator9644, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4822) (by decide : 0 < 667)
        adaptiveSpanProfilesValid9644 adaptiveOrder9644 adaptiveSpanNumericCheck9644_7
        adaptiveSpanEven9644_7 adaptiveSpanWhole9644_7
        adaptiveSpanEvenEntries9644_7 adaptiveSpanWholeEntries9644_7
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanEvenDomain9644_7)
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanWholeDomain9644_7)
  · simpa only [adaptiveSpanLevel9644, adaptiveSpanNumerator9644, adaptiveSpanDenominator9644, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 4822) (by decide : 0 < 899)
        adaptiveSpanProfilesValid9644 adaptiveOrder9644 adaptiveSpanNumericCheck9644_8
        adaptiveSpanEven9644_8 adaptiveSpanWhole9644_8
        adaptiveSpanEvenEntries9644_8 adaptiveSpanWholeEntries9644_8
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanEvenDomain9644_8)
        (by rw [adaptiveSpanProfileLength9644]; exact adaptiveSpanWholeDomain9644_8)

/-- The complete finite histogram certificate for 8768 ≤ n ≤ 9644. -/
theorem adaptiveSpanHistogram9644 : DegreeIntervalCertificate 9644 adaptiveSpanPrimes9644
    (fun s v => sharpDegree (8768 / 2) 7 (adaptiveSpanNumerator9644 s)
      (adaptiveSpanDenominator9644 s) (totientDensity v))
    (fun s v => sharpDegree 8768 7 (adaptiveSpanNumerator9644 s)
      (adaptiveSpanDenominator9644 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows9644)
    adaptiveSpanPrimes9644
    (fun s => sharpDegree (8768 / 2) 7 (adaptiveSpanNumerator9644 s) (adaptiveSpanDenominator9644 s))
    (fun s => sharpDegree 8768 7 (adaptiveSpanNumerator9644 s) (adaptiveSpanDenominator9644 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid9644 adaptiveOrder9644 (coreOrderPermutationCheck_sound adaptivePermutation9644)
    (by rw [adaptiveSpanProfileLength9644]; decide +kernel)
    adaptiveSpanLevel9644 adaptiveSpanTreeCache9644 adaptiveSpanTreeRepresents9644
    (fun j => adaptiveSpanWitness9644.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck9644

/-- Every required odd cycle for a dense set, throughout 8768 ≤ n ≤ 9644. -/
theorem adaptiveSpanInterval9644 {n : ℕ} (hLn : 8768 ≤ n) (hnU : n ≤ 9644)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptiveSpanPrimes9644
    adaptiveSpanNumerator9644 adaptiveSpanDenominator9644 adaptiveSpanSharpTail9644
    adaptiveSpanPrimeSupport9644 adaptiveSpanHistogram9644 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail9644
#print axioms adaptiveSpanPrimeSupport9644
#print axioms adaptiveSpanHistogram9644
#print axioms adaptiveSpanInterval9644
end Erdos883Verified
