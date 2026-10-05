import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate18801Metadata
import Erdos883AdaptiveSpan18801Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate18801PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes18801 : List ℕ := [3, 5, 7, 11, 13, 17, 19]

def adaptiveSpanNumerator18801 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | _ => 616

def adaptiveSpanDenominator18801 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | _ => 667

theorem adaptiveSpanSharpTail18801 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes18801.length) :
    SharpTailCertificate 18801 (adaptiveSpanPrimes18801.take s)
      (adaptiveSpanNumerator18801 s) (adaptiveSpanDenominator18801 s) := by
  have hs' : s ≤ 7 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 18801 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 18801 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 18801 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 18801 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 18801 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 18801 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 18801 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 18801 [3, 5, 7, 11, 13, 17, 19] 616 667
    refine ⟨by decide, {23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport18801 : ∀ u ∈ oddUniverse 18801,
    ∀ v ∈ oddUniverse 18801, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid18801 : AdaptiveProfileRowsValid adaptiveRows18801 :=
  coreProfileMetadataCheck_sound adaptiveMetadata18801

theorem adaptiveSpanProfileLength18801 : adaptiveRows18801.length = halfOdds 18801 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics18801
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache18801 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes18801.length) :
    (adaptiveSpanLevel18801 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel18801 s).2.cacheCheck = true := by
  have hs' : s ≤ 7 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel18801, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache18801_0 adaptiveSpanWholeCache18801_0
  · simpa only [adaptiveSpanLevel18801, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache18801_1 adaptiveSpanWholeCache18801_1
  · simpa only [adaptiveSpanLevel18801, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache18801_2 adaptiveSpanWholeCache18801_2
  · simpa only [adaptiveSpanLevel18801, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache18801_3 adaptiveSpanWholeCache18801_3
  · simpa only [adaptiveSpanLevel18801, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache18801_4 adaptiveSpanWholeCache18801_4
  · simpa only [adaptiveSpanLevel18801, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache18801_5 adaptiveSpanWholeCache18801_5
  · simpa only [adaptiveSpanLevel18801, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache18801_6 adaptiveSpanWholeCache18801_6
  · simpa only [adaptiveSpanLevel18801, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache18801_7 adaptiveSpanWholeCache18801_7

theorem adaptiveSpanTreeRepresents18801 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes18801.length) :
    AdaptiveSpanTreeRepresents adaptiveRows18801 (halfOdds 18801)
      (sharpDegree (17092 / 2) 8 (adaptiveSpanNumerator18801 s) (adaptiveSpanDenominator18801 s))
      (sharpDegree 17092 8 (adaptiveSpanNumerator18801 s) (adaptiveSpanDenominator18801 s))
      (adaptiveSpanLevel18801 s).1 (adaptiveSpanLevel18801 s).2 := by
  have hs' : s ≤ 7 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel18801, adaptiveSpanNumerator18801, adaptiveSpanDenominator18801, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 9401) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid18801 adaptiveOrder18801 adaptiveSpanNumericCheck18801_0
        adaptiveSpanEven18801_0 adaptiveSpanWhole18801_0
        adaptiveSpanEvenEntries18801_0 adaptiveSpanWholeEntries18801_0
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanEvenDomain18801_0)
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanWholeDomain18801_0)
  · simpa only [adaptiveSpanLevel18801, adaptiveSpanNumerator18801, adaptiveSpanDenominator18801, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 9401) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid18801 adaptiveOrder18801 adaptiveSpanNumericCheck18801_1
        adaptiveSpanEven18801_1 adaptiveSpanWhole18801_1
        adaptiveSpanEvenEntries18801_1 adaptiveSpanWholeEntries18801_1
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanEvenDomain18801_1)
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanWholeDomain18801_1)
  · simpa only [adaptiveSpanLevel18801, adaptiveSpanNumerator18801, adaptiveSpanDenominator18801, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 9401) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid18801 adaptiveOrder18801 adaptiveSpanNumericCheck18801_2
        adaptiveSpanEven18801_2 adaptiveSpanWhole18801_2
        adaptiveSpanEvenEntries18801_2 adaptiveSpanWholeEntries18801_2
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanEvenDomain18801_2)
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanWholeDomain18801_2)
  · simpa only [adaptiveSpanLevel18801, adaptiveSpanNumerator18801, adaptiveSpanDenominator18801, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 9401) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid18801 adaptiveOrder18801 adaptiveSpanNumericCheck18801_3
        adaptiveSpanEven18801_3 adaptiveSpanWhole18801_3
        adaptiveSpanEvenEntries18801_3 adaptiveSpanWholeEntries18801_3
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanEvenDomain18801_3)
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanWholeDomain18801_3)
  · simpa only [adaptiveSpanLevel18801, adaptiveSpanNumerator18801, adaptiveSpanDenominator18801, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 9401) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid18801 adaptiveOrder18801 adaptiveSpanNumericCheck18801_4
        adaptiveSpanEven18801_4 adaptiveSpanWhole18801_4
        adaptiveSpanEvenEntries18801_4 adaptiveSpanWholeEntries18801_4
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanEvenDomain18801_4)
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanWholeDomain18801_4)
  · simpa only [adaptiveSpanLevel18801, adaptiveSpanNumerator18801, adaptiveSpanDenominator18801, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 9401) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid18801 adaptiveOrder18801 adaptiveSpanNumericCheck18801_5
        adaptiveSpanEven18801_5 adaptiveSpanWhole18801_5
        adaptiveSpanEvenEntries18801_5 adaptiveSpanWholeEntries18801_5
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanEvenDomain18801_5)
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanWholeDomain18801_5)
  · simpa only [adaptiveSpanLevel18801, adaptiveSpanNumerator18801, adaptiveSpanDenominator18801, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 9401) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid18801 adaptiveOrder18801 adaptiveSpanNumericCheck18801_6
        adaptiveSpanEven18801_6 adaptiveSpanWhole18801_6
        adaptiveSpanEvenEntries18801_6 adaptiveSpanWholeEntries18801_6
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanEvenDomain18801_6)
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanWholeDomain18801_6)
  · simpa only [adaptiveSpanLevel18801, adaptiveSpanNumerator18801, adaptiveSpanDenominator18801, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 9401) (by decide : 0 < 667)
        adaptiveSpanProfilesValid18801 adaptiveOrder18801 adaptiveSpanNumericCheck18801_7
        adaptiveSpanEven18801_7 adaptiveSpanWhole18801_7
        adaptiveSpanEvenEntries18801_7 adaptiveSpanWholeEntries18801_7
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanEvenDomain18801_7)
        (by rw [adaptiveSpanProfileLength18801]; exact adaptiveSpanWholeDomain18801_7)

/-- The complete finite histogram certificate for 17092 ≤ n ≤ 18801. -/
theorem adaptiveSpanHistogram18801 : DegreeIntervalCertificate 18801 adaptiveSpanPrimes18801
    (fun s v => sharpDegree (17092 / 2) 8 (adaptiveSpanNumerator18801 s)
      (adaptiveSpanDenominator18801 s) (totientDensity v))
    (fun s v => sharpDegree 17092 8 (adaptiveSpanNumerator18801 s)
      (adaptiveSpanDenominator18801 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows18801)
    adaptiveSpanPrimes18801
    (fun s => sharpDegree (17092 / 2) 8 (adaptiveSpanNumerator18801 s) (adaptiveSpanDenominator18801 s))
    (fun s => sharpDegree 17092 8 (adaptiveSpanNumerator18801 s) (adaptiveSpanDenominator18801 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid18801 adaptiveOrder18801 adaptivePermutationSemantics18801
    (by rw [adaptiveSpanProfileLength18801]; decide +kernel)
    adaptiveSpanLevel18801 adaptiveSpanTreeCache18801 adaptiveSpanTreeRepresents18801
    (fun j => adaptiveSpanWitness18801.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength18801
  · exact adaptiveSpanWitnessCheck18801

/-- Every required odd cycle for a dense set, throughout 17092 ≤ n ≤ 18801. -/
theorem adaptiveSpanInterval18801 {n : ℕ} (hLn : 17092 ≤ n) (hnU : n ≤ 18801)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes18801
    adaptiveSpanNumerator18801 adaptiveSpanDenominator18801 adaptiveSpanSharpTail18801
    adaptiveSpanPrimeSupport18801 adaptiveSpanHistogram18801 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail18801
#print axioms adaptiveSpanPrimeSupport18801
#print axioms adaptiveSpanHistogram18801
#print axioms adaptiveSpanInterval18801
end Erdos883Verified
