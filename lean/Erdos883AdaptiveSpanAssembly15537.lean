import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate15537Metadata
import Erdos883AdaptiveSpan15537Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate15537PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes15537 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator15537 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 720
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 616
  | _ => 840

def adaptiveSpanDenominator15537 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 1001
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 667
  | _ => 899

theorem adaptiveSpanSharpTail15537 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes15537.length) :
    SharpTailCertificate 15537 (adaptiveSpanPrimes15537.take s)
      (adaptiveSpanNumerator15537 s) (adaptiveSpanDenominator15537 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 15537 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 15537 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 15537 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 15537 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 15537 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 15537 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 15537 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 15537 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 15537 [3, 5, 7, 11, 13, 17, 19, 23] 840 899
    refine ⟨by decide, {29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport15537 : ∀ u ∈ oddUniverse 15537,
    ∀ v ∈ oddUniverse 15537, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid15537 : AdaptiveProfileRowsValid adaptiveRows15537 :=
  coreProfileMetadataCheck_sound adaptiveMetadata15537

theorem adaptiveSpanProfileLength15537 : adaptiveRows15537.length = halfOdds 15537 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics15537
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache15537 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes15537.length) :
    (adaptiveSpanLevel15537 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel15537 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel15537, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache15537_0 adaptiveSpanWholeCache15537_0
  · simpa only [adaptiveSpanLevel15537, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache15537_1 adaptiveSpanWholeCache15537_1
  · simpa only [adaptiveSpanLevel15537, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache15537_2 adaptiveSpanWholeCache15537_2
  · simpa only [adaptiveSpanLevel15537, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache15537_3 adaptiveSpanWholeCache15537_3
  · simpa only [adaptiveSpanLevel15537, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache15537_4 adaptiveSpanWholeCache15537_4
  · simpa only [adaptiveSpanLevel15537, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache15537_5 adaptiveSpanWholeCache15537_5
  · simpa only [adaptiveSpanLevel15537, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache15537_6 adaptiveSpanWholeCache15537_6
  · simpa only [adaptiveSpanLevel15537, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache15537_7 adaptiveSpanWholeCache15537_7
  · simpa only [adaptiveSpanLevel15537, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache15537_8 adaptiveSpanWholeCache15537_8

theorem adaptiveSpanTreeRepresents15537 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes15537.length) :
    AdaptiveSpanTreeRepresents adaptiveRows15537 (halfOdds 15537)
      (sharpDegree (14125 / 2) 8 (adaptiveSpanNumerator15537 s) (adaptiveSpanDenominator15537 s))
      (sharpDegree 14125 8 (adaptiveSpanNumerator15537 s) (adaptiveSpanDenominator15537 s))
      (adaptiveSpanLevel15537 s).1 (adaptiveSpanLevel15537 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel15537, adaptiveSpanNumerator15537, adaptiveSpanDenominator15537, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7769) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid15537 adaptiveOrder15537 adaptiveSpanNumericCheck15537_0
        adaptiveSpanEven15537_0 adaptiveSpanWhole15537_0
        adaptiveSpanEvenEntries15537_0 adaptiveSpanWholeEntries15537_0
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanEvenDomain15537_0)
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanWholeDomain15537_0)
  · simpa only [adaptiveSpanLevel15537, adaptiveSpanNumerator15537, adaptiveSpanDenominator15537, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7769) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid15537 adaptiveOrder15537 adaptiveSpanNumericCheck15537_1
        adaptiveSpanEven15537_1 adaptiveSpanWhole15537_1
        adaptiveSpanEvenEntries15537_1 adaptiveSpanWholeEntries15537_1
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanEvenDomain15537_1)
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanWholeDomain15537_1)
  · simpa only [adaptiveSpanLevel15537, adaptiveSpanNumerator15537, adaptiveSpanDenominator15537, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7769) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid15537 adaptiveOrder15537 adaptiveSpanNumericCheck15537_2
        adaptiveSpanEven15537_2 adaptiveSpanWhole15537_2
        adaptiveSpanEvenEntries15537_2 adaptiveSpanWholeEntries15537_2
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanEvenDomain15537_2)
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanWholeDomain15537_2)
  · simpa only [adaptiveSpanLevel15537, adaptiveSpanNumerator15537, adaptiveSpanDenominator15537, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7769) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid15537 adaptiveOrder15537 adaptiveSpanNumericCheck15537_3
        adaptiveSpanEven15537_3 adaptiveSpanWhole15537_3
        adaptiveSpanEvenEntries15537_3 adaptiveSpanWholeEntries15537_3
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanEvenDomain15537_3)
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanWholeDomain15537_3)
  · simpa only [adaptiveSpanLevel15537, adaptiveSpanNumerator15537, adaptiveSpanDenominator15537, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7769) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid15537 adaptiveOrder15537 adaptiveSpanNumericCheck15537_4
        adaptiveSpanEven15537_4 adaptiveSpanWhole15537_4
        adaptiveSpanEvenEntries15537_4 adaptiveSpanWholeEntries15537_4
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanEvenDomain15537_4)
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanWholeDomain15537_4)
  · simpa only [adaptiveSpanLevel15537, adaptiveSpanNumerator15537, adaptiveSpanDenominator15537, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7769) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid15537 adaptiveOrder15537 adaptiveSpanNumericCheck15537_5
        adaptiveSpanEven15537_5 adaptiveSpanWhole15537_5
        adaptiveSpanEvenEntries15537_5 adaptiveSpanWholeEntries15537_5
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanEvenDomain15537_5)
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanWholeDomain15537_5)
  · simpa only [adaptiveSpanLevel15537, adaptiveSpanNumerator15537, adaptiveSpanDenominator15537, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7769) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid15537 adaptiveOrder15537 adaptiveSpanNumericCheck15537_6
        adaptiveSpanEven15537_6 adaptiveSpanWhole15537_6
        adaptiveSpanEvenEntries15537_6 adaptiveSpanWholeEntries15537_6
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanEvenDomain15537_6)
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanWholeDomain15537_6)
  · simpa only [adaptiveSpanLevel15537, adaptiveSpanNumerator15537, adaptiveSpanDenominator15537, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7769) (by decide : 0 < 667)
        adaptiveSpanProfilesValid15537 adaptiveOrder15537 adaptiveSpanNumericCheck15537_7
        adaptiveSpanEven15537_7 adaptiveSpanWhole15537_7
        adaptiveSpanEvenEntries15537_7 adaptiveSpanWholeEntries15537_7
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanEvenDomain15537_7)
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanWholeDomain15537_7)
  · simpa only [adaptiveSpanLevel15537, adaptiveSpanNumerator15537, adaptiveSpanDenominator15537, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 7769) (by decide : 0 < 899)
        adaptiveSpanProfilesValid15537 adaptiveOrder15537 adaptiveSpanNumericCheck15537_8
        adaptiveSpanEven15537_8 adaptiveSpanWhole15537_8
        adaptiveSpanEvenEntries15537_8 adaptiveSpanWholeEntries15537_8
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanEvenDomain15537_8)
        (by rw [adaptiveSpanProfileLength15537]; exact adaptiveSpanWholeDomain15537_8)

/-- The complete finite histogram certificate for 14125 ≤ n ≤ 15537. -/
theorem adaptiveSpanHistogram15537 : DegreeIntervalCertificate 15537 adaptiveSpanPrimes15537
    (fun s v => sharpDegree (14125 / 2) 8 (adaptiveSpanNumerator15537 s)
      (adaptiveSpanDenominator15537 s) (totientDensity v))
    (fun s v => sharpDegree 14125 8 (adaptiveSpanNumerator15537 s)
      (adaptiveSpanDenominator15537 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows15537)
    adaptiveSpanPrimes15537
    (fun s => sharpDegree (14125 / 2) 8 (adaptiveSpanNumerator15537 s) (adaptiveSpanDenominator15537 s))
    (fun s => sharpDegree 14125 8 (adaptiveSpanNumerator15537 s) (adaptiveSpanDenominator15537 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid15537 adaptiveOrder15537 adaptivePermutationSemantics15537
    (by rw [adaptiveSpanProfileLength15537]; decide +kernel)
    adaptiveSpanLevel15537 adaptiveSpanTreeCache15537 adaptiveSpanTreeRepresents15537
    (fun j => adaptiveSpanWitness15537.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength15537
  · exact adaptiveSpanWitnessCheck15537

/-- Every required odd cycle for a dense set, throughout 14125 ≤ n ≤ 15537. -/
theorem adaptiveSpanInterval15537 {n : ℕ} (hLn : 14125 ≤ n) (hnU : n ≤ 15537)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes15537
    adaptiveSpanNumerator15537 adaptiveSpanDenominator15537 adaptiveSpanSharpTail15537
    adaptiveSpanPrimeSupport15537 adaptiveSpanHistogram15537 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail15537
#print axioms adaptiveSpanPrimeSupport15537
#print axioms adaptiveSpanHistogram15537
#print axioms adaptiveSpanInterval15537
end Erdos883Verified
