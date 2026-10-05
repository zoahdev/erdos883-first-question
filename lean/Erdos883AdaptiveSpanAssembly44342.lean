import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate44342Metadata
import Erdos883AdaptiveSpan44342Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate44342PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes44342 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

def adaptiveSpanNumerator44342 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | _ => 30240

def adaptiveSpanDenominator44342 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | _ => 33263

theorem adaptiveSpanSharpTail44342 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes44342.length) :
    SharpTailCertificate 44342 (adaptiveSpanPrimes44342.take s)
      (adaptiveSpanNumerator44342 s) (adaptiveSpanDenominator44342 s) := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 44342 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 44342 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 44342 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 44342 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 44342 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 44342 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 44342 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 44342 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 44342 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport44342 : ∀ u ∈ oddUniverse 44342,
    ∀ v ∈ oddUniverse 44342, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid44342 : AdaptiveProfileRowsValid adaptiveRows44342 :=
  coreProfileMetadataCheck_sound adaptiveMetadata44342

theorem adaptiveSpanProfileLength44342 : adaptiveRows44342.length = halfOdds 44342 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics44342
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache44342 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes44342.length) :
    (adaptiveSpanLevel44342 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel44342 s).2.cacheCheck = true := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel44342, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache44342_0 adaptiveSpanWholeCache44342_0
  · simpa only [adaptiveSpanLevel44342, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache44342_1 adaptiveSpanWholeCache44342_1
  · simpa only [adaptiveSpanLevel44342, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache44342_2 adaptiveSpanWholeCache44342_2
  · simpa only [adaptiveSpanLevel44342, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache44342_3 adaptiveSpanWholeCache44342_3
  · simpa only [adaptiveSpanLevel44342, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache44342_4 adaptiveSpanWholeCache44342_4
  · simpa only [adaptiveSpanLevel44342, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache44342_5 adaptiveSpanWholeCache44342_5
  · simpa only [adaptiveSpanLevel44342, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache44342_6 adaptiveSpanWholeCache44342_6
  · simpa only [adaptiveSpanLevel44342, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache44342_7 adaptiveSpanWholeCache44342_7
  · simpa only [adaptiveSpanLevel44342, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache44342_8 adaptiveSpanWholeCache44342_8

theorem adaptiveSpanTreeRepresents44342 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes44342.length) :
    AdaptiveSpanTreeRepresents adaptiveRows44342 (halfOdds 44342)
      (sharpDegree (40311 / 2) 8 (adaptiveSpanNumerator44342 s) (adaptiveSpanDenominator44342 s))
      (sharpDegree 40311 8 (adaptiveSpanNumerator44342 s) (adaptiveSpanDenominator44342 s))
      (adaptiveSpanLevel44342 s).1 (adaptiveSpanLevel44342 s).2 := by
  have hs' : s ≤ 8 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel44342, adaptiveSpanNumerator44342, adaptiveSpanDenominator44342, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 22171) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid44342 adaptiveOrder44342 adaptiveSpanNumericCheck44342_0
        adaptiveSpanEven44342_0 adaptiveSpanWhole44342_0
        adaptiveSpanEvenEntries44342_0 adaptiveSpanWholeEntries44342_0
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanEvenDomain44342_0)
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanWholeDomain44342_0)
  · simpa only [adaptiveSpanLevel44342, adaptiveSpanNumerator44342, adaptiveSpanDenominator44342, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 22171) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid44342 adaptiveOrder44342 adaptiveSpanNumericCheck44342_1
        adaptiveSpanEven44342_1 adaptiveSpanWhole44342_1
        adaptiveSpanEvenEntries44342_1 adaptiveSpanWholeEntries44342_1
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanEvenDomain44342_1)
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanWholeDomain44342_1)
  · simpa only [adaptiveSpanLevel44342, adaptiveSpanNumerator44342, adaptiveSpanDenominator44342, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 22171) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid44342 adaptiveOrder44342 adaptiveSpanNumericCheck44342_2
        adaptiveSpanEven44342_2 adaptiveSpanWhole44342_2
        adaptiveSpanEvenEntries44342_2 adaptiveSpanWholeEntries44342_2
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanEvenDomain44342_2)
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanWholeDomain44342_2)
  · simpa only [adaptiveSpanLevel44342, adaptiveSpanNumerator44342, adaptiveSpanDenominator44342, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 22171) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid44342 adaptiveOrder44342 adaptiveSpanNumericCheck44342_3
        adaptiveSpanEven44342_3 adaptiveSpanWhole44342_3
        adaptiveSpanEvenEntries44342_3 adaptiveSpanWholeEntries44342_3
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanEvenDomain44342_3)
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanWholeDomain44342_3)
  · simpa only [adaptiveSpanLevel44342, adaptiveSpanNumerator44342, adaptiveSpanDenominator44342, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 22171) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid44342 adaptiveOrder44342 adaptiveSpanNumericCheck44342_4
        adaptiveSpanEven44342_4 adaptiveSpanWhole44342_4
        adaptiveSpanEvenEntries44342_4 adaptiveSpanWholeEntries44342_4
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanEvenDomain44342_4)
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanWholeDomain44342_4)
  · simpa only [adaptiveSpanLevel44342, adaptiveSpanNumerator44342, adaptiveSpanDenominator44342, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 22171) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid44342 adaptiveOrder44342 adaptiveSpanNumericCheck44342_5
        adaptiveSpanEven44342_5 adaptiveSpanWhole44342_5
        adaptiveSpanEvenEntries44342_5 adaptiveSpanWholeEntries44342_5
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanEvenDomain44342_5)
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanWholeDomain44342_5)
  · simpa only [adaptiveSpanLevel44342, adaptiveSpanNumerator44342, adaptiveSpanDenominator44342, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 22171) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid44342 adaptiveOrder44342 adaptiveSpanNumericCheck44342_6
        adaptiveSpanEven44342_6 adaptiveSpanWhole44342_6
        adaptiveSpanEvenEntries44342_6 adaptiveSpanWholeEntries44342_6
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanEvenDomain44342_6)
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanWholeDomain44342_6)
  · simpa only [adaptiveSpanLevel44342, adaptiveSpanNumerator44342, adaptiveSpanDenominator44342, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 22171) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid44342 adaptiveOrder44342 adaptiveSpanNumericCheck44342_7
        adaptiveSpanEven44342_7 adaptiveSpanWhole44342_7
        adaptiveSpanEvenEntries44342_7 adaptiveSpanWholeEntries44342_7
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanEvenDomain44342_7)
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanWholeDomain44342_7)
  · simpa only [adaptiveSpanLevel44342, adaptiveSpanNumerator44342, adaptiveSpanDenominator44342, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 22171) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid44342 adaptiveOrder44342 adaptiveSpanNumericCheck44342_8
        adaptiveSpanEven44342_8 adaptiveSpanWhole44342_8
        adaptiveSpanEvenEntries44342_8 adaptiveSpanWholeEntries44342_8
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanEvenDomain44342_8)
        (by rw [adaptiveSpanProfileLength44342]; exact adaptiveSpanWholeDomain44342_8)

/-- The complete finite histogram certificate for 40311 ≤ n ≤ 44342. -/
theorem adaptiveSpanHistogram44342 : DegreeIntervalCertificate 44342 adaptiveSpanPrimes44342
    (fun s v => sharpDegree (40311 / 2) 8 (adaptiveSpanNumerator44342 s)
      (adaptiveSpanDenominator44342 s) (totientDensity v))
    (fun s v => sharpDegree 40311 8 (adaptiveSpanNumerator44342 s)
      (adaptiveSpanDenominator44342 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows44342)
    adaptiveSpanPrimes44342
    (fun s => sharpDegree (40311 / 2) 8 (adaptiveSpanNumerator44342 s) (adaptiveSpanDenominator44342 s))
    (fun s => sharpDegree 40311 8 (adaptiveSpanNumerator44342 s) (adaptiveSpanDenominator44342 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid44342 adaptiveOrder44342 adaptivePermutationSemantics44342
    (by rw [adaptiveSpanProfileLength44342]; decide +kernel)
    adaptiveSpanLevel44342 adaptiveSpanTreeCache44342 adaptiveSpanTreeRepresents44342
    (fun j => adaptiveSpanWitness44342.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength44342
  · exact adaptiveSpanWitnessCheck44342

/-- Every required odd cycle for a dense set, throughout 40311 ≤ n ≤ 44342. -/
theorem adaptiveSpanInterval44342 {n : ℕ} (hLn : 40311 ≤ n) (hnU : n ≤ 44342)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes44342
    adaptiveSpanNumerator44342 adaptiveSpanDenominator44342 adaptiveSpanSharpTail44342
    adaptiveSpanPrimeSupport44342 adaptiveSpanHistogram44342 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail44342
#print axioms adaptiveSpanPrimeSupport44342
#print axioms adaptiveSpanHistogram44342
#print axioms adaptiveSpanInterval44342
end Erdos883Verified
