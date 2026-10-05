import Erdos883AdaptiveCertificateAssembly
import Erdos883AdaptiveCertificate1262Metadata
import Erdos883AdaptiveCertificate1262Witness
import Erdos883PrimeSupportBudget

namespace Erdos883Verified

def adaptivePrimes1262 : List ℕ := [3, 5, 7, 11, 13]

def adaptiveNumerator1262 : ℕ → ℕ
  | 0 => 480
  | 1 => 240
  | 2 => 720
  | 3 => 120
  | 4 => 192
  | _ => 288

def adaptiveDenominator1262 : ℕ → ℕ
  | 0 => 1155
  | 1 => 385
  | 2 => 1001
  | 3 => 143
  | 4 => 221
  | _ => 323

theorem adaptiveSharpTail1262 (s : ℕ) (hs : s ≤ adaptivePrimes1262.length) :
    SharpTailCertificate 1262 (adaptivePrimes1262.take s)
      (adaptiveNumerator1262 s) (adaptiveDenominator1262 s) := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · change SharpTailCertificate 1262 [] 480 1155
    refine ⟨by decide, {3, 5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1262 [3] 240 385
    refine ⟨by decide, {5, 7, 11}, 13, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1262 [3, 5] 720 1001
    refine ⟨by decide, {7, 11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1262 [3, 5, 7] 120 143
    refine ⟨by decide, {11, 13}, 17, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1262 [3, 5, 7, 11] 192 221
    refine ⟨by decide, {13, 17}, 19, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num
  · change SharpTailCertificate 1262 [3, 5, 7, 11, 13] 288 323
    refine ⟨by decide, {17, 19}, 23, by decide, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_⟩
    norm_num

theorem adaptivePrimeSupport1262 : ∀ u ∈ oddUniverse 1262,
    ∀ v ∈ oddUniverse 1262, (Nat.lcm u v).primeFactors.card ≤ 6 := by
  intro u hu v hv
  rcases Finset.mem_filter.mp hu with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hv with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU⟩
  have h := odd_lcm_primeFactors_card_le_benchmark (q := 19)
    (by decide) hu hv huodd hvodd huU hvU (by decide +kernel)
  have hc : (oddPrimeBenchmark 19).card = 6 := by decide +kernel
  simpa only [hc] using h

theorem adaptiveProfilesValid1262 : AdaptiveProfileRowsValid adaptiveRows1262 :=
  coreProfileMetadataCheck_sound adaptiveMetadata1262

theorem adaptiveProfileLength1262 : adaptiveRows1262.length = halfOdds 1262 := by
  obtain ⟨hnd, hset⟩ := coreOrderPermutationCheck_sound adaptivePermutation1262
  have hc := List.toFinset_card_of_nodup hnd
  rw [hset, oddUniverse_card] at hc
  simpa only [coreProfileValues, List.length_map] using hc.symm

theorem adaptiveTreeCache1262 (s : ℕ) (hs : s ≤ adaptivePrimes1262.length) :
    (adaptiveLevel1262 s).1.cacheCheck = true ∧
      (adaptiveLevel1262 s).2.cacheCheck = true := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveLevel1262, ↓reduceIte] using
      And.intro adaptiveEvenCache1262_0 adaptiveWholeCache1262_0
  · simpa only [adaptiveLevel1262, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1262_1 adaptiveWholeCache1262_1
  · simpa only [adaptiveLevel1262, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1262_2 adaptiveWholeCache1262_2
  · simpa only [adaptiveLevel1262, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1262_3 adaptiveWholeCache1262_3
  · simpa only [adaptiveLevel1262, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1262_4 adaptiveWholeCache1262_4
  · simpa only [adaptiveLevel1262, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      And.intro adaptiveEvenCache1262_5 adaptiveWholeCache1262_5

theorem adaptiveTreeRepresents1262 (s : ℕ) (hs : s ≤ adaptivePrimes1262.length) :
    AdaptiveTreeRepresents adaptiveRows1262 (halfOdds 1262)
      (sharpDegree (1242 / 2) 6 (adaptiveNumerator1262 s) (adaptiveDenominator1262 s))
      (sharpDegree 1242 6 (adaptiveNumerator1262 s) (adaptiveDenominator1262 s))
      (adaptiveLevel1262 s).1 (adaptiveLevel1262 s).2 := by
  have hs' : s ≤ 5 := hs
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [adaptiveLevel1262, adaptiveNumerator1262, adaptiveDenominator1262, halfOdds, Nat.reduceAdd, Nat.reduceDiv, ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1242 6 480 1155 631
        adaptiveProfilesValid1262 (by decide) adaptiveEven1262_0 adaptiveWhole1262_0
        adaptiveEvenEntries1262_0 adaptiveWholeEntries1262_0
  · simpa only [adaptiveLevel1262, adaptiveNumerator1262, adaptiveDenominator1262, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (1 : ℕ) ≠ 0 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1242 6 240 385 631
        adaptiveProfilesValid1262 (by decide) adaptiveEven1262_1 adaptiveWhole1262_1
        adaptiveEvenEntries1262_1 adaptiveWholeEntries1262_1
  · simpa only [adaptiveLevel1262, adaptiveNumerator1262, adaptiveDenominator1262, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (2 : ℕ) ≠ 0 by decide), (show (2 : ℕ) ≠ 1 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1242 6 720 1001 631
        adaptiveProfilesValid1262 (by decide) adaptiveEven1262_2 adaptiveWhole1262_2
        adaptiveEvenEntries1262_2 adaptiveWholeEntries1262_2
  · simpa only [adaptiveLevel1262, adaptiveNumerator1262, adaptiveDenominator1262, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (3 : ℕ) ≠ 0 by decide), (show (3 : ℕ) ≠ 1 by decide), (show (3 : ℕ) ≠ 2 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1242 6 120 143 631
        adaptiveProfilesValid1262 (by decide) adaptiveEven1262_3 adaptiveWhole1262_3
        adaptiveEvenEntries1262_3 adaptiveWholeEntries1262_3
  · simpa only [adaptiveLevel1262, adaptiveNumerator1262, adaptiveDenominator1262, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (4 : ℕ) ≠ 0 by decide), (show (4 : ℕ) ≠ 1 by decide), (show (4 : ℕ) ≠ 2 by decide), (show (4 : ℕ) ≠ 3 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1242 6 192 221 631
        adaptiveProfilesValid1262 (by decide) adaptiveEven1262_4 adaptiveWhole1262_4
        adaptiveEvenEntries1262_4 adaptiveWholeEntries1262_4
  · simpa only [adaptiveLevel1262, adaptiveNumerator1262, adaptiveDenominator1262, halfOdds, Nat.reduceAdd, Nat.reduceDiv, (show (5 : ℕ) ≠ 0 by decide), (show (5 : ℕ) ≠ 1 by decide), (show (5 : ℕ) ≠ 2 by decide), (show (5 : ℕ) ≠ 3 by decide), (show (5 : ℕ) ≠ 4 by decide), ↓reduceIte] using
      adaptiveTreeRepresents_of_entries 1242 6 288 323 631
        adaptiveProfilesValid1262 (by decide) adaptiveEven1262_5 adaptiveWhole1262_5
        adaptiveEvenEntries1262_5 adaptiveWholeEntries1262_5

/-- The complete finite histogram certificate for 1242 ≤ n ≤ 1262. -/
theorem adaptiveHistogram1262 : DegreeIntervalCertificate 1262 adaptivePrimes1262
    (fun s v => sharpDegree (1242 / 2) 6 (adaptiveNumerator1262 s)
      (adaptiveDenominator1262 s) (totientDensity v))
    (fun s v => sharpDegree 1242 6 (adaptiveNumerator1262 s)
      (adaptiveDenominator1262 s) (totientDensity v)) := by
  apply adaptive_histogram_of_tree_witnesses (rows := adaptiveRows1262)
    adaptivePrimes1262
    (fun s => sharpDegree (1242 / 2) 6 (adaptiveNumerator1262 s) (adaptiveDenominator1262 s))
    (fun s => sharpDegree 1242 6 (adaptiveNumerator1262 s) (adaptiveDenominator1262 s))
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    (fun s _ {_ _} hx hxy => sharpDegree_mono _ _ _ _ hx hxy)
    adaptiveProfilesValid1262 adaptiveOrder1262 adaptivePermutation1262
    (by rw [adaptiveProfileLength1262]; decide +kernel)
    adaptiveLevel1262 adaptiveTreeCache1262 adaptiveTreeRepresents1262
    (fun j => adaptiveWitness1262.getD (j-1) ⟨0,0⟩)
  apply adaptiveWitnessTable_sound
  · decide +kernel
  · exact adaptiveWitnessCheck1262

/-- Every required odd cycle for a dense set, throughout 1242 ≤ n ≤ 1262. -/
theorem adaptiveInterval1262 {n : ℕ} (hLn : 1242 ≤ n) (hnU : n ≤ 1262)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  exact sharp_histogram_interval_sound (by decide) 6 adaptivePrimes1262
    adaptiveNumerator1262 adaptiveDenominator1262 adaptiveSharpTail1262
    adaptivePrimeSupport1262 adaptiveHistogram1262 hLn hnU A hA hdense hk hkn

#print axioms adaptiveSharpTail1262
#print axioms adaptivePrimeSupport1262
#print axioms adaptiveHistogram1262
#print axioms adaptiveInterval1262
end Erdos883Verified
