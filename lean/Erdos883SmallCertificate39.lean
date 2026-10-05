import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder39 : List ℕ := [1, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 25, 35, 3, 9, 27, 39, 33, 21, 15]
theorem smallOrder39_nodup : smallOrder39.Nodup := by decide +kernel
theorem smallOrder39_set : smallOrder39.toFinset = oddUniverse 39 := by decide +kernel

private theorem finiteCheck36_39_b0 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 0 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b1 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 1 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b2 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 2 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b3 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 3 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b4 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 4 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b5 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 5 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b6 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 6 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b7 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 7 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b8 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 8 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b9 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 9 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b10 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 10 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b11 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 11 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

private theorem finiteCheck36_39_b12 :
    ∀ j : Fin 6, ∃ s : Fin 5,
      intervalWitness 36 39 smallOrder39 [3, 5, 7, 11] 12 (j.val + 1) s.val := by
  unfold intervalWitness
  decide +kernel

theorem finiteCheck36_39 : finiteIntervalCheck 36 39 smallOrder39 [3, 5, 7, 11] := by
  intro b j
  fin_cases b
  · exact finiteCheck36_39_b0 j
  · exact finiteCheck36_39_b1 j
  · exact finiteCheck36_39_b2 j
  · exact finiteCheck36_39_b3 j
  · exact finiteCheck36_39_b4 j
  · exact finiteCheck36_39_b5 j
  · exact finiteCheck36_39_b6 j
  · exact finiteCheck36_39_b7 j
  · exact finiteCheck36_39_b8 j
  · exact finiteCheck36_39_b9 j
  · exact finiteCheck36_39_b10 j
  · exact finiteCheck36_39_b11 j
  · exact finiteCheck36_39_b12 j

theorem exactCertificate36_39 : ExactIntervalCertificate 36 39 smallOrder39 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck36_39
#print axioms smallOrder39_nodup
#print axioms smallOrder39_set
#print axioms finiteCheck36_39
#print axioms exactCertificate36_39
end Erdos883Verified
