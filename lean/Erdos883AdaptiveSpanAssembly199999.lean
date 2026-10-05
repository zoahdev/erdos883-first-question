import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate199999Metadata
import Erdos883AdaptiveSpan199999Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate199999PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes199999 : List ℕ := [3, 5, 7, 11, 13, 17, 19]

def adaptiveSpanNumerator199999 : ℕ → ℕ
  | 0 => 5760
  | 1 => 46080
  | 2 => 11520
  | 3 => 34560
  | 4 => 76032
  | 5 => 6336
  | 6 => 11088
  | _ => 18480

def adaptiveSpanDenominator199999 : ℕ → ℕ
  | 0 => 15015
  | 1 => 85085
  | 2 => 17017
  | 3 => 46189
  | 4 => 96577
  | 5 => 7429
  | 6 => 12673
  | _ => 20677

theorem adaptiveSpanSharpTail199999 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes199999.length) :
    SharpTailCertificate 199999 (adaptiveSpanPrimes199999.take s)
      (adaptiveSpanNumerator199999 s) (adaptiveSpanDenominator199999 s) := by
  have hs' : s ≤ 7 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 199999 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 199999 [3] 46080 85085
    refine ⟨by decide, {5, 7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 199999 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 199999 [3, 5, 7] 34560 46189
    refine ⟨by decide, {11, 13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 199999 [3, 5, 7, 11] 76032 96577
    refine ⟨by decide, {13, 17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 199999 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 199999 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 199999 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport199999 : ∀ u ∈ oddUniverse 199999,
    ∀ v ∈ oddUniverse 199999, (Nat.lcm u v).primeFactors.card ≤ 9 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 31)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 31).card = 9 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid199999 : AdaptiveProfileRowsValid adaptiveRows199999 :=
  coreProfileMetadataCheck_sound adaptiveMetadata199999

theorem adaptiveSpanProfileLength199999 : adaptiveRows199999.length = halfOdds 199999 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics199999
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache199999 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes199999.length) :
    (adaptiveSpanLevel199999 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel199999 s).2.cacheCheck = true := by
  have hs' : s ≤ 7 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel199999, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache199999_0 adaptiveSpanWholeCache199999_0
  · simpa only [adaptiveSpanLevel199999, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache199999_1 adaptiveSpanWholeCache199999_1
  · simpa only [adaptiveSpanLevel199999, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache199999_2 adaptiveSpanWholeCache199999_2
  · simpa only [adaptiveSpanLevel199999, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache199999_3 adaptiveSpanWholeCache199999_3
  · simpa only [adaptiveSpanLevel199999, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache199999_4 adaptiveSpanWholeCache199999_4
  · simpa only [adaptiveSpanLevel199999, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache199999_5 adaptiveSpanWholeCache199999_5
  · simpa only [adaptiveSpanLevel199999, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache199999_6 adaptiveSpanWholeCache199999_6
  · simpa only [adaptiveSpanLevel199999, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache199999_7 adaptiveSpanWholeCache199999_7

theorem adaptiveSpanTreeRepresents199999 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes199999.length) :
    AdaptiveSpanTreeRepresents adaptiveRows199999 (halfOdds 199999)
      (sharpDegree (185247 / 2) 9 (adaptiveSpanNumerator199999 s) (adaptiveSpanDenominator199999 s))
      (sharpDegree 185247 9 (adaptiveSpanNumerator199999 s) (adaptiveSpanDenominator199999 s))
      (adaptiveSpanLevel199999 s).1 (adaptiveSpanLevel199999 s).2 := by
  have hs' : s ≤ 7 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel199999, adaptiveSpanNumerator199999, adaptiveSpanDenominator199999, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 100000) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid199999 adaptiveOrder199999 adaptiveSpanNumericCheck199999_0
        adaptiveSpanEven199999_0 adaptiveSpanWhole199999_0
        adaptiveSpanEvenEntries199999_0 adaptiveSpanWholeEntries199999_0
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanEvenDomain199999_0)
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanWholeDomain199999_0)
  · simpa only [adaptiveSpanLevel199999, adaptiveSpanNumerator199999, adaptiveSpanDenominator199999, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 100000) (by decide : 0 < 85085)
        adaptiveSpanProfilesValid199999 adaptiveOrder199999 adaptiveSpanNumericCheck199999_1
        adaptiveSpanEven199999_1 adaptiveSpanWhole199999_1
        adaptiveSpanEvenEntries199999_1 adaptiveSpanWholeEntries199999_1
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanEvenDomain199999_1)
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanWholeDomain199999_1)
  · simpa only [adaptiveSpanLevel199999, adaptiveSpanNumerator199999, adaptiveSpanDenominator199999, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 100000) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid199999 adaptiveOrder199999 adaptiveSpanNumericCheck199999_2
        adaptiveSpanEven199999_2 adaptiveSpanWhole199999_2
        adaptiveSpanEvenEntries199999_2 adaptiveSpanWholeEntries199999_2
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanEvenDomain199999_2)
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanWholeDomain199999_2)
  · simpa only [adaptiveSpanLevel199999, adaptiveSpanNumerator199999, adaptiveSpanDenominator199999, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 100000) (by decide : 0 < 46189)
        adaptiveSpanProfilesValid199999 adaptiveOrder199999 adaptiveSpanNumericCheck199999_3
        adaptiveSpanEven199999_3 adaptiveSpanWhole199999_3
        adaptiveSpanEvenEntries199999_3 adaptiveSpanWholeEntries199999_3
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanEvenDomain199999_3)
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanWholeDomain199999_3)
  · simpa only [adaptiveSpanLevel199999, adaptiveSpanNumerator199999, adaptiveSpanDenominator199999, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 100000) (by decide : 0 < 96577)
        adaptiveSpanProfilesValid199999 adaptiveOrder199999 adaptiveSpanNumericCheck199999_4
        adaptiveSpanEven199999_4 adaptiveSpanWhole199999_4
        adaptiveSpanEvenEntries199999_4 adaptiveSpanWholeEntries199999_4
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanEvenDomain199999_4)
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanWholeDomain199999_4)
  · simpa only [adaptiveSpanLevel199999, adaptiveSpanNumerator199999, adaptiveSpanDenominator199999, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 100000) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid199999 adaptiveOrder199999 adaptiveSpanNumericCheck199999_5
        adaptiveSpanEven199999_5 adaptiveSpanWhole199999_5
        adaptiveSpanEvenEntries199999_5 adaptiveSpanWholeEntries199999_5
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanEvenDomain199999_5)
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanWholeDomain199999_5)
  · simpa only [adaptiveSpanLevel199999, adaptiveSpanNumerator199999, adaptiveSpanDenominator199999, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 100000) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid199999 adaptiveOrder199999 adaptiveSpanNumericCheck199999_6
        adaptiveSpanEven199999_6 adaptiveSpanWhole199999_6
        adaptiveSpanEvenEntries199999_6 adaptiveSpanWholeEntries199999_6
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanEvenDomain199999_6)
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanWholeDomain199999_6)
  · simpa only [adaptiveSpanLevel199999, adaptiveSpanNumerator199999, adaptiveSpanDenominator199999, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 100000) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid199999 adaptiveOrder199999 adaptiveSpanNumericCheck199999_7
        adaptiveSpanEven199999_7 adaptiveSpanWhole199999_7
        adaptiveSpanEvenEntries199999_7 adaptiveSpanWholeEntries199999_7
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanEvenDomain199999_7)
        (by rw [adaptiveSpanProfileLength199999]; exact adaptiveSpanWholeDomain199999_7)

/-- The complete finite histogram certificate for 185247 ≤ n ≤ 199999. -/
theorem adaptiveSpanHistogram199999 : DegreeIntervalCertificate 199999 adaptiveSpanPrimes199999
    (fun s v => sharpDegree (185247 / 2) 9 (adaptiveSpanNumerator199999 s)
      (adaptiveSpanDenominator199999 s) (totientDensity v))
    (fun s v => sharpDegree 185247 9 (adaptiveSpanNumerator199999 s)
      (adaptiveSpanDenominator199999 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows199999)
    adaptiveSpanPrimes199999
    (fun s => sharpDegree (185247 / 2) 9 (adaptiveSpanNumerator199999 s) (adaptiveSpanDenominator199999 s))
    (fun s => sharpDegree 185247 9 (adaptiveSpanNumerator199999 s) (adaptiveSpanDenominator199999 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid199999 adaptiveOrder199999 adaptivePermutationSemantics199999
    (by rw [adaptiveSpanProfileLength199999]; decide +kernel)
    adaptiveSpanLevel199999 adaptiveSpanTreeCache199999 adaptiveSpanTreeRepresents199999
    (fun j => adaptiveSpanWitness199999.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength199999
  · exact adaptiveSpanWitnessCheck199999

/-- Every required odd cycle for a dense set, throughout 185247 ≤ n ≤ 199999. -/
theorem adaptiveSpanInterval199999 {n : ℕ} (hLn : 185247 ≤ n) (hnU : n ≤ 199999)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 9 adaptiveSpanPrimes199999
    adaptiveSpanNumerator199999 adaptiveSpanDenominator199999 adaptiveSpanSharpTail199999
    adaptiveSpanPrimeSupport199999 adaptiveSpanHistogram199999 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail199999
#print axioms adaptiveSpanPrimeSupport199999
#print axioms adaptiveSpanHistogram199999
#print axioms adaptiveSpanInterval199999
end Erdos883Verified
