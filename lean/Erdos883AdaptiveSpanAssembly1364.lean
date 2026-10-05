import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate1364Metadata
import Erdos883AdaptiveSpan1364Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptiveSpanPrimes1364 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveSpanNumerator1364 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveSpanDenominator1364 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSpanSharpTail1364 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1364.length) :
    SharpTailCertificate 1364 (adaptiveSpanPrimes1364.take s)
      (adaptiveSpanNumerator1364 s) (adaptiveSpanDenominator1364 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1364 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1364 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1364 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1364 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1364 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1364 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport1364 : ∀ u ∈ oddUniverse 1364,
    ∀ v ∈ oddUniverse 1364, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid1364 : AdaptiveProfileRowsValid adaptiveRows1364 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1364

theorem adaptiveSpanProfileLength1364 : adaptiveRows1364.length = halfOdds 1364 := by
  obtain ⟨hnd, hset⟩ := (coreOrderPermutationCheck_sound adaptivePermutation1364)
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache1364 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1364.length) :
    (adaptiveSpanLevel1364 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel1364 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1364, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1364_0 adaptiveSpanWholeCache1364_0
  · simpa only [adaptiveSpanLevel1364, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1364_1 adaptiveSpanWholeCache1364_1
  · simpa only [adaptiveSpanLevel1364, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1364_2 adaptiveSpanWholeCache1364_2
  · simpa only [adaptiveSpanLevel1364, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1364_3 adaptiveSpanWholeCache1364_3
  · simpa only [adaptiveSpanLevel1364, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1364_4 adaptiveSpanWholeCache1364_4
  · simpa only [adaptiveSpanLevel1364, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache1364_5 adaptiveSpanWholeCache1364_5

theorem adaptiveSpanTreeRepresents1364 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes1364.length) :
    AdaptiveSpanTreeRepresents adaptiveRows1364 (halfOdds 1364)
      (sharpDegree (1334 / 2) 6 (adaptiveSpanNumerator1364 s) (adaptiveSpanDenominator1364 s))
      (sharpDegree 1334 6 (adaptiveSpanNumerator1364 s) (adaptiveSpanDenominator1364 s))
      (adaptiveSpanLevel1364 s).1 (adaptiveSpanLevel1364 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel1364, adaptiveSpanNumerator1364, adaptiveSpanDenominator1364, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 682) (by decide : 0 < 1155)
        adaptiveSpanProfilesValid1364 adaptiveOrder1364 adaptiveSpanNumericCheck1364_0
        adaptiveSpanEven1364_0 adaptiveSpanWhole1364_0
        adaptiveSpanEvenEntries1364_0 adaptiveSpanWholeEntries1364_0
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanEvenDomain1364_0)
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanWholeDomain1364_0)
  · simpa only [adaptiveSpanLevel1364, adaptiveSpanNumerator1364, adaptiveSpanDenominator1364, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 682) (by decide : 0 < 385)
        adaptiveSpanProfilesValid1364 adaptiveOrder1364 adaptiveSpanNumericCheck1364_1
        adaptiveSpanEven1364_1 adaptiveSpanWhole1364_1
        adaptiveSpanEvenEntries1364_1 adaptiveSpanWholeEntries1364_1
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanEvenDomain1364_1)
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanWholeDomain1364_1)
  · simpa only [adaptiveSpanLevel1364, adaptiveSpanNumerator1364, adaptiveSpanDenominator1364, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 682) (by decide : 0 < 1001)
        adaptiveSpanProfilesValid1364 adaptiveOrder1364 adaptiveSpanNumericCheck1364_2
        adaptiveSpanEven1364_2 adaptiveSpanWhole1364_2
        adaptiveSpanEvenEntries1364_2 adaptiveSpanWholeEntries1364_2
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanEvenDomain1364_2)
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanWholeDomain1364_2)
  · simpa only [adaptiveSpanLevel1364, adaptiveSpanNumerator1364, adaptiveSpanDenominator1364, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 682) (by decide : 0 < 143)
        adaptiveSpanProfilesValid1364 adaptiveOrder1364 adaptiveSpanNumericCheck1364_3
        adaptiveSpanEven1364_3 adaptiveSpanWhole1364_3
        adaptiveSpanEvenEntries1364_3 adaptiveSpanWholeEntries1364_3
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanEvenDomain1364_3)
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanWholeDomain1364_3)
  · simpa only [adaptiveSpanLevel1364, adaptiveSpanNumerator1364, adaptiveSpanDenominator1364, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 682) (by decide : 0 < 221)
        adaptiveSpanProfilesValid1364 adaptiveOrder1364 adaptiveSpanNumericCheck1364_4
        adaptiveSpanEven1364_4 adaptiveSpanWhole1364_4
        adaptiveSpanEvenEntries1364_4 adaptiveSpanWholeEntries1364_4
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanEvenDomain1364_4)
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanWholeDomain1364_4)
  · simpa only [adaptiveSpanLevel1364, adaptiveSpanNumerator1364, adaptiveSpanDenominator1364, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 682) (by decide : 0 < 323)
        adaptiveSpanProfilesValid1364 adaptiveOrder1364 adaptiveSpanNumericCheck1364_5
        adaptiveSpanEven1364_5 adaptiveSpanWhole1364_5
        adaptiveSpanEvenEntries1364_5 adaptiveSpanWholeEntries1364_5
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanEvenDomain1364_5)
        (by rw [adaptiveSpanProfileLength1364]; exact adaptiveSpanWholeDomain1364_5)

/-- The complete finite histogram certificate for 1334 ≤ n ≤ 1364. -/
theorem adaptiveSpanHistogram1364 : DegreeIntervalCertificate 1364 adaptiveSpanPrimes1364
    (fun s v => sharpDegree (1334 / 2) 6 (adaptiveSpanNumerator1364 s)
      (adaptiveSpanDenominator1364 s) (totientDensity v))
    (fun s v => sharpDegree 1334 6 (adaptiveSpanNumerator1364 s)
      (adaptiveSpanDenominator1364 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows1364)
    adaptiveSpanPrimes1364
    (fun s => sharpDegree (1334 / 2) 6 (adaptiveSpanNumerator1364 s) (adaptiveSpanDenominator1364 s))
    (fun s => sharpDegree 1334 6 (adaptiveSpanNumerator1364 s) (adaptiveSpanDenominator1364 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid1364 adaptiveOrder1364 (coreOrderPermutationCheck_sound adaptivePermutation1364)
    (by rw [adaptiveSpanProfileLength1364]; decide +kernel)
    adaptiveSpanLevel1364 adaptiveSpanTreeCache1364 adaptiveSpanTreeRepresents1364
    (fun j => adaptiveSpanWitness1364.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · decide +kernel
  · exact adaptiveSpanWitnessCheck1364

/-- Every required odd cycle for a dense set, throughout 1334 ≤ n ≤ 1364. -/
theorem adaptiveSpanInterval1364 {n : ℕ} (hLn : 1334 ≤ n) (hnU : n ≤ 1364)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptiveSpanPrimes1364
    adaptiveSpanNumerator1364 adaptiveSpanDenominator1364 adaptiveSpanSharpTail1364
    adaptiveSpanPrimeSupport1364 adaptiveSpanHistogram1364 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail1364
#print axioms adaptiveSpanPrimeSupport1364
#print axioms adaptiveSpanHistogram1364
#print axioms adaptiveSpanInterval1364
end Erdos883Verified
