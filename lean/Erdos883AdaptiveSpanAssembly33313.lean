import Erdos883AdaptiveSpanRows
import Erdos883AdaptiveCertificate33313Metadata
import Erdos883AdaptiveSpan33313Witness
import Erdos883PrimeSupportBudget
import Erdos883AdaptiveCertificate33313PermutationSemantic

namespace Erdos883Verified

def adaptiveSpanPrimes33313 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29]

def adaptiveSpanNumerator33313 : ℕ → ℕ
  | 0 => 5760
  | 1 => 2880
  | 2 => 11520
  | 3 => 1920
  | 4 => 3456
  | 5 => 6336
  | 6 => 11088
  | 7 => 18480
  | 8 => 30240
  | _ => 1080

def adaptiveSpanDenominator33313 : ℕ → ℕ
  | 0 => 15015
  | 1 => 5005
  | 2 => 17017
  | 3 => 2431
  | 4 => 4199
  | 5 => 7429
  | 6 => 12673
  | 7 => 20677
  | 8 => 33263
  | _ => 1147

theorem adaptiveSpanSharpTail33313 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes33313.length) :
    SharpTailCertificate 33313 (adaptiveSpanPrimes33313.take s)
      (adaptiveSpanNumerator33313 s) (adaptiveSpanDenominator33313 s) := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 33313 [] 5760 15015
    refine ⟨by decide, {3, 5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 33313 [3] 2880 5005
    refine ⟨by decide, {5, 7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 33313 [3, 5] 11520 17017
    refine ⟨by decide, {7, 11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 33313 [3, 5, 7] 1920 2431
    refine ⟨by decide, {11, 13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 33313 [3, 5, 7, 11] 3456 4199
    refine ⟨by decide, {13, 17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 33313 [3, 5, 7, 11, 13] 6336 7429
    refine ⟨by decide, {17, 19, 23}, 29, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 33313 [3, 5, 7, 11, 13, 17] 11088 12673
    refine ⟨by decide, {19, 23, 29}, 31, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 33313 [3, 5, 7, 11, 13, 17, 19] 18480 20677
    refine ⟨by decide, {23, 29, 31}, 37, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 33313 [3, 5, 7, 11, 13, 17, 19, 23] 30240 33263
    refine ⟨by decide, {29, 31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 33313 [3, 5, 7, 11, 13, 17, 19, 23, 29] 1080 1147
    refine ⟨by decide, {31, 37}, 41, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptiveSpanPrimeSupport33313 : ∀ u ∈ oddUniverse 33313,
    ∀ v ∈ oddUniverse 33313, (Nat.lcm u v).primeFactors.card ≤ 8 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 29)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 29).card = 8 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveSpanProfilesValid33313 : AdaptiveProfileRowsValid adaptiveRows33313 :=
  coreProfileMetadataCheck_sound adaptiveMetadata33313

theorem adaptiveSpanProfileLength33313 : adaptiveRows33313.length = halfOdds 33313 := by
  obtain ⟨hnd, hset⟩ := adaptivePermutationSemantics33313
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveSpanTreeCache33313 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes33313.length) :
    (adaptiveSpanLevel33313 s).1.cacheCheck = true ∧
      (adaptiveSpanLevel33313 s).2.cacheCheck = true := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel33313, ↓reduceIte] using
      And.intro adaptiveSpanEvenCache33313_0 adaptiveSpanWholeCache33313_0
  · simpa only [adaptiveSpanLevel33313, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache33313_1 adaptiveSpanWholeCache33313_1
  · simpa only [adaptiveSpanLevel33313, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache33313_2 adaptiveSpanWholeCache33313_2
  · simpa only [adaptiveSpanLevel33313, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache33313_3 adaptiveSpanWholeCache33313_3
  · simpa only [adaptiveSpanLevel33313, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache33313_4 adaptiveSpanWholeCache33313_4
  · simpa only [adaptiveSpanLevel33313, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache33313_5 adaptiveSpanWholeCache33313_5
  · simpa only [adaptiveSpanLevel33313, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache33313_6 adaptiveSpanWholeCache33313_6
  · simpa only [adaptiveSpanLevel33313, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache33313_7 adaptiveSpanWholeCache33313_7
  · simpa only [adaptiveSpanLevel33313, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache33313_8 adaptiveSpanWholeCache33313_8
  · simpa only [adaptiveSpanLevel33313, (show (9 : ℕ) ≠ 0 by decide), (show (9 : ℕ) ≠ 1 by decide), (show (9 : ℕ) ≠ 2 by decide), (show (9 : ℕ) ≠ 3 by decide), (show (9 : ℕ) ≠ 4 by decide), (show (9 : ℕ) ≠ 5 by decide), (show (9 : ℕ) ≠ 6 by decide), (show (9 : ℕ) ≠ 7 by decide), (show (9 : ℕ) ≠ 8 by decide), ↓reduceIte] using
      And.intro adaptiveSpanEvenCache33313_9 adaptiveSpanWholeCache33313_9

theorem adaptiveSpanTreeRepresents33313 (s : ℕ) (hs : s ≤ adaptiveSpanPrimes33313.length) :
    AdaptiveSpanTreeRepresents adaptiveRows33313 (halfOdds 33313)
      (sharpDegree (30285 / 2) 8 (adaptiveSpanNumerator33313 s) (adaptiveSpanDenominator33313 s))
      (sharpDegree 30285 8 (adaptiveSpanNumerator33313 s) (adaptiveSpanDenominator33313 s))
      (adaptiveSpanLevel33313 s).1 (adaptiveSpanLevel33313 s).2 := by
  have hs' : s ≤ 9 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveSpanLevel33313, adaptiveSpanNumerator33313, adaptiveSpanDenominator33313, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 16657) (by decide : 0 < 15015)
        adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptiveSpanNumericCheck33313_0
        adaptiveSpanEven33313_0 adaptiveSpanWhole33313_0
        adaptiveSpanEvenEntries33313_0 adaptiveSpanWholeEntries33313_0
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanEvenDomain33313_0)
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanWholeDomain33313_0)
  · simpa only [adaptiveSpanLevel33313, adaptiveSpanNumerator33313, adaptiveSpanDenominator33313, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 16657) (by decide : 0 < 5005)
        adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptiveSpanNumericCheck33313_1
        adaptiveSpanEven33313_1 adaptiveSpanWhole33313_1
        adaptiveSpanEvenEntries33313_1 adaptiveSpanWholeEntries33313_1
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanEvenDomain33313_1)
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanWholeDomain33313_1)
  · simpa only [adaptiveSpanLevel33313, adaptiveSpanNumerator33313, adaptiveSpanDenominator33313, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 16657) (by decide : 0 < 17017)
        adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptiveSpanNumericCheck33313_2
        adaptiveSpanEven33313_2 adaptiveSpanWhole33313_2
        adaptiveSpanEvenEntries33313_2 adaptiveSpanWholeEntries33313_2
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanEvenDomain33313_2)
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanWholeDomain33313_2)
  · simpa only [adaptiveSpanLevel33313, adaptiveSpanNumerator33313, adaptiveSpanDenominator33313, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 16657) (by decide : 0 < 2431)
        adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptiveSpanNumericCheck33313_3
        adaptiveSpanEven33313_3 adaptiveSpanWhole33313_3
        adaptiveSpanEvenEntries33313_3 adaptiveSpanWholeEntries33313_3
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanEvenDomain33313_3)
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanWholeDomain33313_3)
  · simpa only [adaptiveSpanLevel33313, adaptiveSpanNumerator33313, adaptiveSpanDenominator33313, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 16657) (by decide : 0 < 4199)
        adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptiveSpanNumericCheck33313_4
        adaptiveSpanEven33313_4 adaptiveSpanWhole33313_4
        adaptiveSpanEvenEntries33313_4 adaptiveSpanWholeEntries33313_4
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanEvenDomain33313_4)
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanWholeDomain33313_4)
  · simpa only [adaptiveSpanLevel33313, adaptiveSpanNumerator33313, adaptiveSpanDenominator33313, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 16657) (by decide : 0 < 7429)
        adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptiveSpanNumericCheck33313_5
        adaptiveSpanEven33313_5 adaptiveSpanWhole33313_5
        adaptiveSpanEvenEntries33313_5 adaptiveSpanWholeEntries33313_5
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanEvenDomain33313_5)
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanWholeDomain33313_5)
  · simpa only [adaptiveSpanLevel33313, adaptiveSpanNumerator33313, adaptiveSpanDenominator33313, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (6 : ℕ) ≠ 0 by decide), (show (6 : ℕ) ≠ 1 by decide), (show (6 : ℕ) ≠ 2 by decide), (show (6 : ℕ) ≠ 3 by decide), (show (6 : ℕ) ≠ 4 by decide), (show (6 : ℕ) ≠ 5 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 16657) (by decide : 0 < 12673)
        adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptiveSpanNumericCheck33313_6
        adaptiveSpanEven33313_6 adaptiveSpanWhole33313_6
        adaptiveSpanEvenEntries33313_6 adaptiveSpanWholeEntries33313_6
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanEvenDomain33313_6)
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanWholeDomain33313_6)
  · simpa only [adaptiveSpanLevel33313, adaptiveSpanNumerator33313, adaptiveSpanDenominator33313, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (7 : ℕ) ≠ 0 by decide), (show (7 : ℕ) ≠ 1 by decide), (show (7 : ℕ) ≠ 2 by decide), (show (7 : ℕ) ≠ 3 by decide), (show (7 : ℕ) ≠ 4 by decide), (show (7 : ℕ) ≠ 5 by decide), (show (7 : ℕ) ≠ 6 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 16657) (by decide : 0 < 20677)
        adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptiveSpanNumericCheck33313_7
        adaptiveSpanEven33313_7 adaptiveSpanWhole33313_7
        adaptiveSpanEvenEntries33313_7 adaptiveSpanWholeEntries33313_7
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanEvenDomain33313_7)
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanWholeDomain33313_7)
  · simpa only [adaptiveSpanLevel33313, adaptiveSpanNumerator33313, adaptiveSpanDenominator33313, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (8 : ℕ) ≠ 0 by decide), (show (8 : ℕ) ≠ 1 by decide), (show (8 : ℕ) ≠ 2 by decide), (show (8 : ℕ) ≠ 3 by decide), (show (8 : ℕ) ≠ 4 by decide), (show (8 : ℕ) ≠ 5 by decide), (show (8 : ℕ) ≠ 6 by decide), (show (8 : ℕ) ≠ 7 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 16657) (by decide : 0 < 33263)
        adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptiveSpanNumericCheck33313_8
        adaptiveSpanEven33313_8 adaptiveSpanWhole33313_8
        adaptiveSpanEvenEntries33313_8 adaptiveSpanWholeEntries33313_8
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanEvenDomain33313_8)
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanWholeDomain33313_8)
  · simpa only [adaptiveSpanLevel33313, adaptiveSpanNumerator33313, adaptiveSpanDenominator33313, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (9 : ℕ) ≠ 0 by decide), (show (9 : ℕ) ≠ 1 by decide), (show (9 : ℕ) ≠ 2 by decide), (show (9 : ℕ) ≠ 3 by decide), (show (9 : ℕ) ≠ 4 by decide), (show (9 : ℕ) ≠ 5 by decide), (show (9 : ℕ) ≠ 6 by decide), (show (9 : ℕ) ≠ 7 by decide), (show (9 : ℕ) ≠ 8 by decide), ↓reduceIte] using
      adaptiveSpanTreeRepresents_of_numericCheck (H := 16657) (by decide : 0 < 1147)
        adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptiveSpanNumericCheck33313_9
        adaptiveSpanEven33313_9 adaptiveSpanWhole33313_9
        adaptiveSpanEvenEntries33313_9 adaptiveSpanWholeEntries33313_9
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanEvenDomain33313_9)
        (by rw [adaptiveSpanProfileLength33313]; exact adaptiveSpanWholeDomain33313_9)

/-- The complete finite histogram certificate for 30285 ≤ n ≤ 33313. -/
theorem adaptiveSpanHistogram33313 : DegreeIntervalCertificate 33313 adaptiveSpanPrimes33313
    (fun s v => sharpDegree (30285 / 2) 8 (adaptiveSpanNumerator33313 s)
      (adaptiveSpanDenominator33313 s) (totientDensity v))
    (fun s v => sharpDegree 30285 8 (adaptiveSpanNumerator33313 s)
      (adaptiveSpanDenominator33313 s) (totientDensity v)) := by
  apply adaptive_histogram_of_span_tree_witnesses (rows := adaptiveRows33313)
    adaptiveSpanPrimes33313
    (fun s => sharpDegree (30285 / 2) 8 (adaptiveSpanNumerator33313 s) (adaptiveSpanDenominator33313 s))
    (fun s => sharpDegree 30285 8 (adaptiveSpanNumerator33313 s) (adaptiveSpanDenominator33313 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveSpanProfilesValid33313 adaptiveOrder33313 adaptivePermutationSemantics33313
    (by rw [adaptiveSpanProfileLength33313]; decide +kernel)
    adaptiveSpanLevel33313 adaptiveSpanTreeCache33313 adaptiveSpanTreeRepresents33313
    (fun j => adaptiveSpanWitness33313.getD (j-1) ⟨0,0⟩)
  apply adaptiveSpanWitnessTable_sound
  · exact adaptiveSpanWitnessLength33313
  · exact adaptiveSpanWitnessCheck33313

/-- Every required odd cycle for a dense set, throughout 30285 ≤ n ≤ 33313. -/
theorem adaptiveSpanInterval33313 {n : ℕ} (hLn : 30285 ≤ n) (hnU : n ≤ 33313)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 8 adaptiveSpanPrimes33313
    adaptiveSpanNumerator33313 adaptiveSpanDenominator33313 adaptiveSpanSharpTail33313
    adaptiveSpanPrimeSupport33313 adaptiveSpanHistogram33313 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSpanSharpTail33313
#print axioms adaptiveSpanPrimeSupport33313
#print axioms adaptiveSpanHistogram33313
#print axioms adaptiveSpanInterval33313
end Erdos883Verified
