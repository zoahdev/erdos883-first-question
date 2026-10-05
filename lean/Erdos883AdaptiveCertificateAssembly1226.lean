import Erdos883AdaptiveCertificateAssembly
import Erdos883AdaptiveCertificate1226Metadata
import Erdos883AdaptiveCertificate1226Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptivePrimes1226 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveNumerator1226 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveDenominator1226 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSharpTail1226 (s : ℕ) (hs : s ≤ adaptivePrimes1226.length) :
    SharpTailCertificate 1226 (adaptivePrimes1226.take s)
      (adaptiveNumerator1226 s) (adaptiveDenominator1226 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1226 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1226 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1226 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1226 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1226 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1226 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptivePrimeSupport1226 : ∀ u ∈ oddUniverse 1226,
    ∀ v ∈ oddUniverse 1226, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveProfilesValid1226 : AdaptiveProfileRowsValid adaptiveRows1226 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1226

theorem adaptiveProfileLength1226 : adaptiveRows1226.length = halfOdds 1226 := by
  obtain ⟨hnd, hset⟩ := coreOrderPermutationCheck_sound adaptivePermutation1226
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveTreeCache1226 (s : ℕ) (hs : s ≤ adaptivePrimes1226.length) :
    (adaptiveLevel1226 s).1.cacheCheck = true ∧
      (adaptiveLevel1226 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveLevel1226, ↓reduceIte] using
      And.intro adaptiveEvenCache1226_0 adaptiveWholeCache1226_0
  · simpa only [adaptiveLevel1226, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1226_1 adaptiveWholeCache1226_1
  · simpa only [adaptiveLevel1226, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1226_2 adaptiveWholeCache1226_2
  · simpa only [adaptiveLevel1226, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1226_3 adaptiveWholeCache1226_3
  · simpa only [adaptiveLevel1226, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1226_4 adaptiveWholeCache1226_4
  · simpa only [adaptiveLevel1226, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1226_5 adaptiveWholeCache1226_5

theorem adaptiveTreeRepresents1226 (s : ℕ) (hs : s ≤ adaptivePrimes1226.length) :
    AdaptiveTreeRepresents adaptiveRows1226 (halfOdds 1226)
      (sharpDegree (1212 / 2) 6 (adaptiveNumerator1226 s) (adaptiveDenominator1226 s))
      (sharpDegree 1212 6 (adaptiveNumerator1226 s) (adaptiveDenominator1226 s))
      (adaptiveLevel1226 s).1 (adaptiveLevel1226 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveLevel1226, adaptiveNumerator1226, adaptiveDenominator1226, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1212 6 480 1155 613
        adaptiveProfilesValid1226 (by decide) adaptiveEven1226_0 adaptiveWhole1226_0
        adaptiveEvenEntries1226_0 adaptiveWholeEntries1226_0
  · simpa only [adaptiveLevel1226, adaptiveNumerator1226, adaptiveDenominator1226, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1212 6 240 385 613
        adaptiveProfilesValid1226 (by decide) adaptiveEven1226_1 adaptiveWhole1226_1
        adaptiveEvenEntries1226_1 adaptiveWholeEntries1226_1
  · simpa only [adaptiveLevel1226, adaptiveNumerator1226, adaptiveDenominator1226, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1212 6 720 1001 613
        adaptiveProfilesValid1226 (by decide) adaptiveEven1226_2 adaptiveWhole1226_2
        adaptiveEvenEntries1226_2 adaptiveWholeEntries1226_2
  · simpa only [adaptiveLevel1226, adaptiveNumerator1226, adaptiveDenominator1226, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1212 6 120 143 613
        adaptiveProfilesValid1226 (by decide) adaptiveEven1226_3 adaptiveWhole1226_3
        adaptiveEvenEntries1226_3 adaptiveWholeEntries1226_3
  · simpa only [adaptiveLevel1226, adaptiveNumerator1226, adaptiveDenominator1226, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1212 6 192 221 613
        adaptiveProfilesValid1226 (by decide) adaptiveEven1226_4 adaptiveWhole1226_4
        adaptiveEvenEntries1226_4 adaptiveWholeEntries1226_4
  · simpa only [adaptiveLevel1226, adaptiveNumerator1226, adaptiveDenominator1226, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1212 6 288 323 613
        adaptiveProfilesValid1226 (by decide) adaptiveEven1226_5 adaptiveWhole1226_5
        adaptiveEvenEntries1226_5 adaptiveWholeEntries1226_5

/-- The complete finite histogram certificate for 1212 ≤ n ≤ 1226. -/
theorem adaptiveHistogram1226 : DegreeIntervalCertificate 1226 adaptivePrimes1226
    (fun s v => sharpDegree (1212 / 2) 6 (adaptiveNumerator1226 s)
      (adaptiveDenominator1226 s) (totientDensity v))
    (fun s v => sharpDegree 1212 6 (adaptiveNumerator1226 s)
      (adaptiveDenominator1226 s) (totientDensity v)) := by
  apply adaptive_histogram_of_tree_witnesses (rows := adaptiveRows1226)
    adaptivePrimes1226
    (fun s => sharpDegree (1212 / 2) 6 (adaptiveNumerator1226 s) (adaptiveDenominator1226 s))
    (fun s => sharpDegree 1212 6 (adaptiveNumerator1226 s) (adaptiveDenominator1226 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveProfilesValid1226 adaptiveOrder1226 adaptivePermutation1226
    (by rw [adaptiveProfileLength1226]; decide +kernel)
    adaptiveLevel1226 adaptiveTreeCache1226 adaptiveTreeRepresents1226
    (fun j => adaptiveWitness1226.getD (j-1) ⟨0,0⟩)
  apply adaptiveWitnessTable_sound
  · decide +kernel
  · exact adaptiveWitnessCheck1226

/-- Every required odd cycle for a dense set, throughout 1212 ≤ n ≤ 1226. -/
theorem adaptiveInterval1226 {n : ℕ} (hLn : 1212 ≤ n) (hnU : n ≤ 1226)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptivePrimes1226
    adaptiveNumerator1226 adaptiveDenominator1226 adaptiveSharpTail1226
    adaptivePrimeSupport1226 adaptiveHistogram1226 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSharpTail1226
#print axioms adaptivePrimeSupport1226
#print axioms adaptiveHistogram1226
#print axioms adaptiveInterval1226
end Erdos883Verified
