import Erdos883AdaptiveCertificateAssembly
import Erdos883AdaptiveCertificate2417Metadata
import Erdos883AdaptiveCertificate2417Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptivePrimes2417 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveNumerator2417 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveDenominator2417 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSharpTail2417 (s : ℕ) (hs : s ≤ adaptivePrimes2417.length) :
    SharpTailCertificate 2417 (adaptivePrimes2417.take s)
      (adaptiveNumerator2417 s) (adaptiveDenominator2417 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 2417 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2417 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2417 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2417 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2417 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 2417 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptivePrimeSupport2417 : ∀ u ∈ oddUniverse 2417,
    ∀ v ∈ oddUniverse 2417, (Nat.lcm u v).primeFactors.card ≤ 7 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 23)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 23).card = 7 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveProfilesValid2417 : AdaptiveProfileRowsValid adaptiveRows2417 :=
  coreProfileMetadataCheck_sound adaptiveMetadata2417

theorem adaptiveProfileLength2417 : adaptiveRows2417.length = halfOdds 2417 := by
  obtain ⟨hnd, hset⟩ := coreOrderPermutationCheck_sound adaptivePermutation2417
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveTreeCache2417 (s : ℕ) (hs : s ≤ adaptivePrimes2417.length) :
    (adaptiveLevel2417 s).1.cacheCheck = true ∧
      (adaptiveLevel2417 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveLevel2417, ↓reduceIte] using
      And.intro adaptiveEvenCache2417_0 adaptiveWholeCache2417_0
  · simpa only [adaptiveLevel2417, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache2417_1 adaptiveWholeCache2417_1
  · simpa only [adaptiveLevel2417, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache2417_2 adaptiveWholeCache2417_2
  · simpa only [adaptiveLevel2417, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache2417_3 adaptiveWholeCache2417_3
  · simpa only [adaptiveLevel2417, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache2417_4 adaptiveWholeCache2417_4
  · simpa only [adaptiveLevel2417, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache2417_5 adaptiveWholeCache2417_5

theorem adaptiveTreeRepresents2417 (s : ℕ) (hs : s ≤ adaptivePrimes2417.length) :
    AdaptiveTreeRepresents adaptiveRows2417 (halfOdds 2417)
      (sharpDegree (2359 / 2) 7 (adaptiveNumerator2417 s) (adaptiveDenominator2417 s))
      (sharpDegree 2359 7 (adaptiveNumerator2417 s) (adaptiveDenominator2417 s))
      (adaptiveLevel2417 s).1 (adaptiveLevel2417 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveLevel2417, adaptiveNumerator2417, adaptiveDenominator2417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 2359 7 480 1155 1209
        adaptiveProfilesValid2417 (by decide) adaptiveEven2417_0 adaptiveWhole2417_0
        adaptiveEvenEntries2417_0 adaptiveWholeEntries2417_0
  · simpa only [adaptiveLevel2417, adaptiveNumerator2417, adaptiveDenominator2417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 2359 7 240 385 1209
        adaptiveProfilesValid2417 (by decide) adaptiveEven2417_1 adaptiveWhole2417_1
        adaptiveEvenEntries2417_1 adaptiveWholeEntries2417_1
  · simpa only [adaptiveLevel2417, adaptiveNumerator2417, adaptiveDenominator2417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 2359 7 720 1001 1209
        adaptiveProfilesValid2417 (by decide) adaptiveEven2417_2 adaptiveWhole2417_2
        adaptiveEvenEntries2417_2 adaptiveWholeEntries2417_2
  · simpa only [adaptiveLevel2417, adaptiveNumerator2417, adaptiveDenominator2417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 2359 7 120 143 1209
        adaptiveProfilesValid2417 (by decide) adaptiveEven2417_3 adaptiveWhole2417_3
        adaptiveEvenEntries2417_3 adaptiveWholeEntries2417_3
  · simpa only [adaptiveLevel2417, adaptiveNumerator2417, adaptiveDenominator2417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 2359 7 192 221 1209
        adaptiveProfilesValid2417 (by decide) adaptiveEven2417_4 adaptiveWhole2417_4
        adaptiveEvenEntries2417_4 adaptiveWholeEntries2417_4
  · simpa only [adaptiveLevel2417, adaptiveNumerator2417, adaptiveDenominator2417, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 2359 7 288 323 1209
        adaptiveProfilesValid2417 (by decide) adaptiveEven2417_5 adaptiveWhole2417_5
        adaptiveEvenEntries2417_5 adaptiveWholeEntries2417_5

/-- The complete finite histogram certificate for 2359 ≤ n ≤ 2417. -/
theorem adaptiveHistogram2417 : DegreeIntervalCertificate 2417 adaptivePrimes2417
    (fun s v => sharpDegree (2359 / 2) 7 (adaptiveNumerator2417 s)
      (adaptiveDenominator2417 s) (totientDensity v))
    (fun s v => sharpDegree 2359 7 (adaptiveNumerator2417 s)
      (adaptiveDenominator2417 s) (totientDensity v)) := by
  apply adaptive_histogram_of_tree_witnesses (rows := adaptiveRows2417)
    adaptivePrimes2417
    (fun s => sharpDegree (2359 / 2) 7 (adaptiveNumerator2417 s) (adaptiveDenominator2417 s))
    (fun s => sharpDegree 2359 7 (adaptiveNumerator2417 s) (adaptiveDenominator2417 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveProfilesValid2417 adaptiveOrder2417 adaptivePermutation2417
    (by rw [adaptiveProfileLength2417]; decide +kernel)
    adaptiveLevel2417 adaptiveTreeCache2417 adaptiveTreeRepresents2417
    (fun j => adaptiveWitness2417.getD (j-1) ⟨0,0⟩)
  apply adaptiveWitnessTable_sound
  · decide +kernel
  · exact adaptiveWitnessCheck2417

/-- Every required odd cycle for a dense set, throughout 2359 ≤ n ≤ 2417. -/
theorem adaptiveInterval2417 {n : ℕ} (hLn : 2359 ≤ n) (hnU : n ≤ 2417)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 7 adaptivePrimes2417
    adaptiveNumerator2417 adaptiveDenominator2417 adaptiveSharpTail2417
    adaptivePrimeSupport2417 adaptiveHistogram2417 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSharpTail2417
#print axioms adaptivePrimeSupport2417
#print axioms adaptiveHistogram2417
#print axioms adaptiveInterval2417
end Erdos883Verified
