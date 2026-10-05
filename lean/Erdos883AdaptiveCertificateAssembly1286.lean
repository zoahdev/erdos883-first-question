import Erdos883AdaptiveCertificateAssembly
import Erdos883AdaptiveCertificate1286Metadata
import Erdos883AdaptiveCertificate1286Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptivePrimes1286 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveNumerator1286 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveDenominator1286 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSharpTail1286 (s : ℕ) (hs : s ≤ adaptivePrimes1286.length) :
    SharpTailCertificate 1286 (adaptivePrimes1286.take s)
      (adaptiveNumerator1286 s) (adaptiveDenominator1286 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1286 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1286 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1286 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1286 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1286 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1286 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptivePrimeSupport1286 : ∀ u ∈ oddUniverse 1286,
    ∀ v ∈ oddUniverse 1286, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveProfilesValid1286 : AdaptiveProfileRowsValid adaptiveRows1286 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1286

theorem adaptiveProfileLength1286 : adaptiveRows1286.length = halfOdds 1286 := by
  obtain ⟨hnd, hset⟩ := coreOrderPermutationCheck_sound adaptivePermutation1286
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveTreeCache1286 (s : ℕ) (hs : s ≤ adaptivePrimes1286.length) :
    (adaptiveLevel1286 s).1.cacheCheck = true ∧
      (adaptiveLevel1286 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveLevel1286, ↓reduceIte] using
      And.intro adaptiveEvenCache1286_0 adaptiveWholeCache1286_0
  · simpa only [adaptiveLevel1286, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1286_1 adaptiveWholeCache1286_1
  · simpa only [adaptiveLevel1286, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1286_2 adaptiveWholeCache1286_2
  · simpa only [adaptiveLevel1286, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1286_3 adaptiveWholeCache1286_3
  · simpa only [adaptiveLevel1286, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1286_4 adaptiveWholeCache1286_4
  · simpa only [adaptiveLevel1286, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1286_5 adaptiveWholeCache1286_5

theorem adaptiveTreeRepresents1286 (s : ℕ) (hs : s ≤ adaptivePrimes1286.length) :
    AdaptiveTreeRepresents adaptiveRows1286 (halfOdds 1286)
      (sharpDegree (1263 / 2) 6 (adaptiveNumerator1286 s) (adaptiveDenominator1286 s))
      (sharpDegree 1263 6 (adaptiveNumerator1286 s) (adaptiveDenominator1286 s))
      (adaptiveLevel1286 s).1 (adaptiveLevel1286 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveLevel1286, adaptiveNumerator1286, adaptiveDenominator1286, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1263 6 480 1155 643
        adaptiveProfilesValid1286 (by decide) adaptiveEven1286_0 adaptiveWhole1286_0
        adaptiveEvenEntries1286_0 adaptiveWholeEntries1286_0
  · simpa only [adaptiveLevel1286, adaptiveNumerator1286, adaptiveDenominator1286, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1263 6 240 385 643
        adaptiveProfilesValid1286 (by decide) adaptiveEven1286_1 adaptiveWhole1286_1
        adaptiveEvenEntries1286_1 adaptiveWholeEntries1286_1
  · simpa only [adaptiveLevel1286, adaptiveNumerator1286, adaptiveDenominator1286, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1263 6 720 1001 643
        adaptiveProfilesValid1286 (by decide) adaptiveEven1286_2 adaptiveWhole1286_2
        adaptiveEvenEntries1286_2 adaptiveWholeEntries1286_2
  · simpa only [adaptiveLevel1286, adaptiveNumerator1286, adaptiveDenominator1286, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1263 6 120 143 643
        adaptiveProfilesValid1286 (by decide) adaptiveEven1286_3 adaptiveWhole1286_3
        adaptiveEvenEntries1286_3 adaptiveWholeEntries1286_3
  · simpa only [adaptiveLevel1286, adaptiveNumerator1286, adaptiveDenominator1286, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1263 6 192 221 643
        adaptiveProfilesValid1286 (by decide) adaptiveEven1286_4 adaptiveWhole1286_4
        adaptiveEvenEntries1286_4 adaptiveWholeEntries1286_4
  · simpa only [adaptiveLevel1286, adaptiveNumerator1286, adaptiveDenominator1286, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1263 6 288 323 643
        adaptiveProfilesValid1286 (by decide) adaptiveEven1286_5 adaptiveWhole1286_5
        adaptiveEvenEntries1286_5 adaptiveWholeEntries1286_5

/-- The complete finite histogram certificate for 1263 ≤ n ≤ 1286. -/
theorem adaptiveHistogram1286 : DegreeIntervalCertificate 1286 adaptivePrimes1286
    (fun s v => sharpDegree (1263 / 2) 6 (adaptiveNumerator1286 s)
      (adaptiveDenominator1286 s) (totientDensity v))
    (fun s v => sharpDegree 1263 6 (adaptiveNumerator1286 s)
      (adaptiveDenominator1286 s) (totientDensity v)) := by
  apply adaptive_histogram_of_tree_witnesses (rows := adaptiveRows1286)
    adaptivePrimes1286
    (fun s => sharpDegree (1263 / 2) 6 (adaptiveNumerator1286 s) (adaptiveDenominator1286 s))
    (fun s => sharpDegree 1263 6 (adaptiveNumerator1286 s) (adaptiveDenominator1286 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveProfilesValid1286 adaptiveOrder1286 adaptivePermutation1286
    (by rw [adaptiveProfileLength1286]; decide +kernel)
    adaptiveLevel1286 adaptiveTreeCache1286 adaptiveTreeRepresents1286
    (fun j => adaptiveWitness1286.getD (j-1) ⟨0,0⟩)
  apply adaptiveWitnessTable_sound
  · decide +kernel
  · exact adaptiveWitnessCheck1286

/-- Every required odd cycle for a dense set, throughout 1263 ≤ n ≤ 1286. -/
theorem adaptiveInterval1286 {n : ℕ} (hLn : 1263 ≤ n) (hnU : n ≤ 1286)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptivePrimes1286
    adaptiveNumerator1286 adaptiveDenominator1286 adaptiveSharpTail1286
    adaptivePrimeSupport1286 adaptiveHistogram1286 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSharpTail1286
#print axioms adaptivePrimeSupport1286
#print axioms adaptiveHistogram1286
#print axioms adaptiveInterval1286
end Erdos883Verified
