import Erdos883FiniteCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder44 : List ℕ := [1, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 25, 35, 3, 9, 27, 39, 33, 21, 15]
theorem smallOrder44_nodup : smallOrder44.Nodup := by decide +kernel
theorem smallOrder44_set : smallOrder44.toFinset = oddUniverse 44 := by decide +kernel

private def signatureWitness44_0 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b0 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      0 (j.val + 1) (signatureWitness44_0 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_1 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b1 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      1 (j.val + 1) (signatureWitness44_1 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_2 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b2 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      2 (j.val + 1) (signatureWitness44_2 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_3 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 1

private theorem intervalWitness40_44_b3 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      3 (j.val + 1) (signatureWitness44_3 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_4 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | _ => 0

private theorem intervalWitness40_44_b4 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      4 (j.val + 1) (signatureWitness44_4 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_5 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b5 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      5 (j.val + 1) (signatureWitness44_5 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_6 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b6 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      6 (j.val + 1) (signatureWitness44_6 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_7 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b7 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      7 (j.val + 1) (signatureWitness44_7 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_8 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b8 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      8 (j.val + 1) (signatureWitness44_8 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_9 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b9 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      9 (j.val + 1) (signatureWitness44_9 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_10 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b10 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      10 (j.val + 1) (signatureWitness44_10 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_11 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b11 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      11 (j.val + 1) (signatureWitness44_11 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_12 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b12 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      12 (j.val + 1) (signatureWitness44_12 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_13 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b13 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      13 (j.val + 1) (signatureWitness44_13 j).val := by
  unfold intervalWitness
  decide +kernel

private def signatureWitness44_14 (j : Fin 7) : Fin 5 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private theorem intervalWitness40_44_b14 :
    ∀ j : Fin 7, intervalWitness 40 44 smallOrder44 [3, 5, 7, 11]
      14 (j.val + 1) (signatureWitness44_14 j).val := by
  unfold intervalWitness
  decide +kernel

theorem finiteCheck40_44 : finiteIntervalCheck 40 44 smallOrder44 [3, 5, 7, 11] := by
  intro b j
  fin_cases b
  · exact ⟨signatureWitness44_0 j, intervalWitness40_44_b0 j⟩
  · exact ⟨signatureWitness44_1 j, intervalWitness40_44_b1 j⟩
  · exact ⟨signatureWitness44_2 j, intervalWitness40_44_b2 j⟩
  · exact ⟨signatureWitness44_3 j, intervalWitness40_44_b3 j⟩
  · exact ⟨signatureWitness44_4 j, intervalWitness40_44_b4 j⟩
  · exact ⟨signatureWitness44_5 j, intervalWitness40_44_b5 j⟩
  · exact ⟨signatureWitness44_6 j, intervalWitness40_44_b6 j⟩
  · exact ⟨signatureWitness44_7 j, intervalWitness40_44_b7 j⟩
  · exact ⟨signatureWitness44_8 j, intervalWitness40_44_b8 j⟩
  · exact ⟨signatureWitness44_9 j, intervalWitness40_44_b9 j⟩
  · exact ⟨signatureWitness44_10 j, intervalWitness40_44_b10 j⟩
  · exact ⟨signatureWitness44_11 j, intervalWitness40_44_b11 j⟩
  · exact ⟨signatureWitness44_12 j, intervalWitness40_44_b12 j⟩
  · exact ⟨signatureWitness44_13 j, intervalWitness40_44_b13 j⟩
  · exact ⟨signatureWitness44_14 j, intervalWitness40_44_b14 j⟩

theorem exactCertificate40_44 : ExactIntervalCertificate 40 44 smallOrder44 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck40_44
#print axioms smallOrder44_nodup
#print axioms smallOrder44_set
#print axioms finiteCheck40_44
#print axioms exactCertificate40_44
end Erdos883Verified
