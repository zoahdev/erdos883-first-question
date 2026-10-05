import Erdos883AdaptiveCertificateAssembly
import Erdos883AdaptiveCertificate1241Metadata
import Erdos883AdaptiveCertificate1241Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptivePrimes1241 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveNumerator1241 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveDenominator1241 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSharpTail1241 (s : ℕ) (hs : s ≤ adaptivePrimes1241.length) :
    SharpTailCertificate 1241 (adaptivePrimes1241.take s)
      (adaptiveNumerator1241 s) (adaptiveDenominator1241 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1241 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1241 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1241 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1241 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1241 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1241 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptivePrimeSupport1241 : ∀ u ∈ oddUniverse 1241,
    ∀ v ∈ oddUniverse 1241, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveProfilesValid1241 : AdaptiveProfileRowsValid adaptiveRows1241 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1241

theorem adaptiveProfileLength1241 : adaptiveRows1241.length = halfOdds 1241 := by
  obtain ⟨hnd, hset⟩ := coreOrderPermutationCheck_sound adaptivePermutation1241
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveTreeCache1241 (s : ℕ) (hs : s ≤ adaptivePrimes1241.length) :
    (adaptiveLevel1241 s).1.cacheCheck = true ∧
      (adaptiveLevel1241 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveLevel1241, ↓reduceIte] using
      And.intro adaptiveEvenCache1241_0 adaptiveWholeCache1241_0
  · simpa only [adaptiveLevel1241, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1241_1 adaptiveWholeCache1241_1
  · simpa only [adaptiveLevel1241, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1241_2 adaptiveWholeCache1241_2
  · simpa only [adaptiveLevel1241, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1241_3 adaptiveWholeCache1241_3
  · simpa only [adaptiveLevel1241, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1241_4 adaptiveWholeCache1241_4
  · simpa only [adaptiveLevel1241, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1241_5 adaptiveWholeCache1241_5

theorem adaptiveTreeRepresents1241 (s : ℕ) (hs : s ≤ adaptivePrimes1241.length) :
    AdaptiveTreeRepresents adaptiveRows1241 (halfOdds 1241)
      (sharpDegree (1227 / 2) 6 (adaptiveNumerator1241 s) (adaptiveDenominator1241 s))
      (sharpDegree 1227 6 (adaptiveNumerator1241 s) (adaptiveDenominator1241 s))
      (adaptiveLevel1241 s).1 (adaptiveLevel1241 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveLevel1241, adaptiveNumerator1241, adaptiveDenominator1241, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1227 6 480 1155 621
        adaptiveProfilesValid1241 (by decide) adaptiveEven1241_0 adaptiveWhole1241_0
        adaptiveEvenEntries1241_0 adaptiveWholeEntries1241_0
  · simpa only [adaptiveLevel1241, adaptiveNumerator1241, adaptiveDenominator1241, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1227 6 240 385 621
        adaptiveProfilesValid1241 (by decide) adaptiveEven1241_1 adaptiveWhole1241_1
        adaptiveEvenEntries1241_1 adaptiveWholeEntries1241_1
  · simpa only [adaptiveLevel1241, adaptiveNumerator1241, adaptiveDenominator1241, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1227 6 720 1001 621
        adaptiveProfilesValid1241 (by decide) adaptiveEven1241_2 adaptiveWhole1241_2
        adaptiveEvenEntries1241_2 adaptiveWholeEntries1241_2
  · simpa only [adaptiveLevel1241, adaptiveNumerator1241, adaptiveDenominator1241, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1227 6 120 143 621
        adaptiveProfilesValid1241 (by decide) adaptiveEven1241_3 adaptiveWhole1241_3
        adaptiveEvenEntries1241_3 adaptiveWholeEntries1241_3
  · simpa only [adaptiveLevel1241, adaptiveNumerator1241, adaptiveDenominator1241, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1227 6 192 221 621
        adaptiveProfilesValid1241 (by decide) adaptiveEven1241_4 adaptiveWhole1241_4
        adaptiveEvenEntries1241_4 adaptiveWholeEntries1241_4
  · simpa only [adaptiveLevel1241, adaptiveNumerator1241, adaptiveDenominator1241, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1227 6 288 323 621
        adaptiveProfilesValid1241 (by decide) adaptiveEven1241_5 adaptiveWhole1241_5
        adaptiveEvenEntries1241_5 adaptiveWholeEntries1241_5

/-- The complete finite histogram certificate for 1227 ≤ n ≤ 1241. -/
theorem adaptiveHistogram1241 : DegreeIntervalCertificate 1241 adaptivePrimes1241
    (fun s v => sharpDegree (1227 / 2) 6 (adaptiveNumerator1241 s)
      (adaptiveDenominator1241 s) (totientDensity v))
    (fun s v => sharpDegree 1227 6 (adaptiveNumerator1241 s)
      (adaptiveDenominator1241 s) (totientDensity v)) := by
  apply adaptive_histogram_of_tree_witnesses (rows := adaptiveRows1241)
    adaptivePrimes1241
    (fun s => sharpDegree (1227 / 2) 6 (adaptiveNumerator1241 s) (adaptiveDenominator1241 s))
    (fun s => sharpDegree 1227 6 (adaptiveNumerator1241 s) (adaptiveDenominator1241 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveProfilesValid1241 adaptiveOrder1241 adaptivePermutation1241
    (by rw [adaptiveProfileLength1241]; decide +kernel)
    adaptiveLevel1241 adaptiveTreeCache1241 adaptiveTreeRepresents1241
    (fun j => adaptiveWitness1241.getD (j-1) ⟨0,0⟩)
  apply adaptiveWitnessTable_sound
  · decide +kernel
  · exact adaptiveWitnessCheck1241

/-- Every required odd cycle for a dense set, throughout 1227 ≤ n ≤ 1241. -/
theorem adaptiveInterval1241 {n : ℕ} (hLn : 1227 ≤ n) (hnU : n ≤ 1241)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptivePrimes1241
    adaptiveNumerator1241 adaptiveDenominator1241 adaptiveSharpTail1241
    adaptivePrimeSupport1241 adaptiveHistogram1241 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSharpTail1241
#print axioms adaptivePrimeSupport1241
#print axioms adaptiveHistogram1241
#print axioms adaptiveInterval1241
end Erdos883Verified
