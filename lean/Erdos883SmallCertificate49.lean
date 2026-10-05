import Erdos883SmallCertificateHelpers
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder49 : List ℕ := [1, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 49, 5, 25, 35, 3, 9, 27, 39, 33, 21, 15, 45]
theorem smallOrder49_nodup : smallOrder49.Nodup := by decide +kernel
theorem smallOrder49_set : smallOrder49.toFinset = oddUniverse 49 := by decide +kernel

private def resources49 (i : Fin 12) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨25, 0, 8, true⟩
  | 1 => ⟨21, 0, 9, true⟩
  | 2 => ⟨20, 0, 10, true⟩
  | 3 => ⟨20, 1, 13, true⟩
  | 4 => ⟨17, 0, 13, true⟩
  | 5 => ⟨16, 0, 15, true⟩
  | 6 => ⟨14, 0, 17, true⟩
  | 7 => ⟨12, 0, 19, true⟩
  | 8 => ⟨11, 0, 20, true⟩
  | 9 => ⟨9, 0, 21, true⟩
  | 10 => ⟨8, 0, 22, true⟩
  | _ => ⟨7, 0, 43, false⟩

private theorem validResource49_0 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 0) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_1 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 1) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_2 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 2) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_3 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 3) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_4 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 4) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_5 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 5) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_6 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 6) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_7 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 7) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_8 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 8) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_9 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 9) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_10 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 10) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource49_11 :
    PrefixResourceValid 45 smallOrder49 [3, 5, 7, 11] (resources49 11) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private def resourceSelector49_0 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | _ => 0

private theorem resourceRequirements45_49_b0 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 0 (j.val + 1)
      (resources49 (resourceSelector49_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_1 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | _ => 1

private theorem resourceRequirements45_49_b1 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 1 (j.val + 1)
      (resources49 (resourceSelector49_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_2 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 1
  | 6 => 2
  | _ => 2

private theorem resourceRequirements45_49_b2 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 2 (j.val + 1)
      (resources49 (resourceSelector49_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_3 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 3

private theorem resourceRequirements45_49_b3 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 3 (j.val + 1)
      (resources49 (resourceSelector49_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_4 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | _ => 3

private theorem resourceRequirements45_49_b4 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 4 (j.val + 1)
      (resources49 (resourceSelector49_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_5 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | _ => 4

private theorem resourceRequirements45_49_b5 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 5 (j.val + 1)
      (resources49 (resourceSelector49_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_6 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 5
  | _ => 5

private theorem resourceRequirements45_49_b6 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 6 (j.val + 1)
      (resources49 (resourceSelector49_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_7 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 4
  | 3 => 4
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | _ => 5

private theorem resourceRequirements45_49_b7 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 7 (j.val + 1)
      (resources49 (resourceSelector49_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_8 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 4
  | 1 => 4
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 6
  | _ => 6

private theorem resourceRequirements45_49_b8 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 8 (j.val + 1)
      (resources49 (resourceSelector49_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_9 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 6
  | 5 => 6
  | 6 => 6
  | _ => 6

private theorem resourceRequirements45_49_b9 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 9 (j.val + 1)
      (resources49 (resourceSelector49_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_10 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 6
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | 6 => 7
  | _ => 7

private theorem resourceRequirements45_49_b10 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 10 (j.val + 1)
      (resources49 (resourceSelector49_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_11 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | 3 => 6
  | 4 => 7
  | 5 => 7
  | 6 => 8
  | _ => 8

private theorem resourceRequirements45_49_b11 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 11 (j.val + 1)
      (resources49 (resourceSelector49_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_12 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 7
  | 3 => 7
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | _ => 8

private theorem resourceRequirements45_49_b12 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 12 (j.val + 1)
      (resources49 (resourceSelector49_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_13 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 7
  | 1 => 7
  | 2 => 8
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 9
  | _ => 9

private theorem resourceRequirements45_49_b13 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 13 (j.val + 1)
      (resources49 (resourceSelector49_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_14 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 8
  | 3 => 8
  | 4 => 9
  | 5 => 9
  | 6 => 10
  | _ => 10

private theorem resourceRequirements45_49_b14 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 14 (j.val + 1)
      (resources49 (resourceSelector49_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_15 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 9
  | 3 => 9
  | 4 => 10
  | 5 => 10
  | 6 => 10
  | _ => 11

private theorem resourceRequirements45_49_b15 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 15 (j.val + 1)
      (resources49 (resourceSelector49_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49_16 (j : Fin 8) : Fin 12 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 10
  | 3 => 10
  | 4 => 10
  | 5 => 10
  | 6 => 11
  | _ => 11

private theorem resourceRequirements45_49_b16 :
    ∀ j : Fin 8, ResourceRequirements 49 [3, 5, 7, 11] 16 (j.val + 1)
      (resources49 (resourceSelector49_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector49 (b : Fin 17) (j : Fin 8) : Fin 12 :=
  match b.val with
  | 0 => resourceSelector49_0 j
  | 1 => resourceSelector49_1 j
  | 2 => resourceSelector49_2 j
  | 3 => resourceSelector49_3 j
  | 4 => resourceSelector49_4 j
  | 5 => resourceSelector49_5 j
  | 6 => resourceSelector49_6 j
  | 7 => resourceSelector49_7 j
  | 8 => resourceSelector49_8 j
  | 9 => resourceSelector49_9 j
  | 10 => resourceSelector49_10 j
  | 11 => resourceSelector49_11 j
  | 12 => resourceSelector49_12 j
  | 13 => resourceSelector49_13 j
  | 14 => resourceSelector49_14 j
  | 15 => resourceSelector49_15 j
  | _ => resourceSelector49_16 j

theorem finiteCheck45_49 : finiteIntervalCheck 45 49 smallOrder49 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 45) (U := 49) (O := smallOrder49) (ps := [3, 5, 7, 11]) resources49 resourceSelector49
  · intro i
    fin_cases i
    · exact validResource49_0
    · exact validResource49_1
    · exact validResource49_2
    · exact validResource49_3
    · exact validResource49_4
    · exact validResource49_5
    · exact validResource49_6
    · exact validResource49_7
    · exact validResource49_8
    · exact validResource49_9
    · exact validResource49_10
    · exact validResource49_11
  · intro b j
    fin_cases b
    · exact resourceRequirements45_49_b0 j
    · exact resourceRequirements45_49_b1 j
    · exact resourceRequirements45_49_b2 j
    · exact resourceRequirements45_49_b3 j
    · exact resourceRequirements45_49_b4 j
    · exact resourceRequirements45_49_b5 j
    · exact resourceRequirements45_49_b6 j
    · exact resourceRequirements45_49_b7 j
    · exact resourceRequirements45_49_b8 j
    · exact resourceRequirements45_49_b9 j
    · exact resourceRequirements45_49_b10 j
    · exact resourceRequirements45_49_b11 j
    · exact resourceRequirements45_49_b12 j
    · exact resourceRequirements45_49_b13 j
    · exact resourceRequirements45_49_b14 j
    · exact resourceRequirements45_49_b15 j
    · exact resourceRequirements45_49_b16 j

theorem exactCertificate45_49 : ExactIntervalCertificate 45 49 smallOrder49 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck45_49
#print axioms smallOrder49_nodup
#print axioms smallOrder49_set
#print axioms finiteCheck45_49
#print axioms exactCertificate45_49
end Erdos883Verified
