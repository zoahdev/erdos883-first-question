import Erdos883SmallCertificateHelpers
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder68 : List ℕ := [1, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 49, 5, 25, 65, 55, 35, 3, 9, 27, 57, 51, 39, 33, 21, 63, 15, 45]
theorem smallOrder68_nodup : smallOrder68.Nodup := by decide +kernel
theorem smallOrder68_set : smallOrder68.toFinset = oddUniverse 68 := by decide +kernel

private def resources68 (i : Fin 13) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨34, 0, 12, true⟩
  | 1 => ⟨28, 0, 13, true⟩
  | 2 => ⟨26, 0, 14, true⟩
  | 3 => ⟨27, 1, 19, true⟩
  | 4 => ⟨23, 0, 19, true⟩
  | 5 => ⟨20, 0, 21, true⟩
  | 6 => ⟨18, 0, 25, true⟩
  | 7 => ⟨16, 0, 27, true⟩
  | 8 => ⟨15, 0, 28, true⟩
  | 9 => ⟨14, 0, 29, true⟩
  | 10 => ⟨10, 0, 30, true⟩
  | 11 => ⟨9, 0, 31, true⟩
  | _ => ⟨8, 0, 60, false⟩

private theorem validResource68_0 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 0) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_1 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 1) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_2 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 2) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_3 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 3) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_4 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 4) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_5 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 5) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_6 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 6) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_7 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 7) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_8 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 8) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_9 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 9) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_10 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 10) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_11 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 11) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource68_12 :
    PrefixResourceValid 62 smallOrder68 [3, 5, 7, 11] (resources68 12) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private def resourceSelector68_0 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | _ => 0

private theorem resourceRequirements62_68_b0 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 0 (j.val + 1)
      (resources68 (resourceSelector68_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_1 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | _ => 1

private theorem resourceRequirements62_68_b1 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 1 (j.val + 1)
      (resources68 (resourceSelector68_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_2 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 1
  | 9 => 1
  | _ => 1

private theorem resourceRequirements62_68_b2 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 2 (j.val + 1)
      (resources68 (resourceSelector68_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_3 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | _ => 2

private theorem resourceRequirements62_68_b3 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 3 (j.val + 1)
      (resources68 (resourceSelector68_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_4 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | _ => 3

private theorem resourceRequirements62_68_b4 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 4 (j.val + 1)
      (resources68 (resourceSelector68_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_5 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 2
  | 7 => 2
  | 8 => 2
  | 9 => 3
  | _ => 3

private theorem resourceRequirements62_68_b5 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 5 (j.val + 1)
      (resources68 (resourceSelector68_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_6 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 3
  | 9 => 3
  | _ => 4

private theorem resourceRequirements62_68_b6 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 6 (j.val + 1)
      (resources68 (resourceSelector68_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_7 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 3
  | 8 => 4
  | 9 => 4
  | _ => 4

private theorem resourceRequirements62_68_b7 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 7 (j.val + 1)
      (resources68 (resourceSelector68_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_8 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 4
  | 7 => 4
  | 8 => 4
  | 9 => 4
  | _ => 4

private theorem resourceRequirements62_68_b8 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 8 (j.val + 1)
      (resources68 (resourceSelector68_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_9 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | 7 => 4
  | 8 => 4
  | 9 => 4
  | _ => 5

private theorem resourceRequirements62_68_b9 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 9 (j.val + 1)
      (resources68 (resourceSelector68_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_10 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | 7 => 4
  | 8 => 5
  | 9 => 5
  | _ => 5

private theorem resourceRequirements62_68_b10 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 10 (j.val + 1)
      (resources68 (resourceSelector68_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_11 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 4
  | 1 => 4
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 5
  | 7 => 5
  | 8 => 5
  | 9 => 5
  | _ => 6

private theorem resourceRequirements62_68_b11 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 11 (j.val + 1)
      (resources68 (resourceSelector68_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_12 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 4
  | 1 => 4
  | 2 => 4
  | 3 => 4
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | 7 => 5
  | 8 => 6
  | 9 => 6
  | _ => 6

private theorem resourceRequirements62_68_b12 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 12 (j.val + 1)
      (resources68 (resourceSelector68_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_13 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 4
  | 1 => 4
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 6
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | _ => 7

private theorem resourceRequirements62_68_b13 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 13 (j.val + 1)
      (resources68 (resourceSelector68_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_14 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 6
  | 5 => 6
  | 6 => 6
  | 7 => 6
  | 8 => 7
  | 9 => 7
  | _ => 8

private theorem resourceRequirements62_68_b14 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 14 (j.val + 1)
      (resources68 (resourceSelector68_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_15 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 6
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | 6 => 7
  | 7 => 7
  | 8 => 8
  | 9 => 8
  | _ => 9

private theorem resourceRequirements62_68_b15 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 15 (j.val + 1)
      (resources68 (resourceSelector68_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_16 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | 3 => 6
  | 4 => 7
  | 5 => 7
  | 6 => 8
  | 7 => 8
  | 8 => 9
  | 9 => 9
  | _ => 9

private theorem resourceRequirements62_68_b16 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 16 (j.val + 1)
      (resources68 (resourceSelector68_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_17 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 7
  | 3 => 7
  | 4 => 8
  | 5 => 8
  | 6 => 9
  | 7 => 9
  | 8 => 9
  | 9 => 9
  | _ => 9

private theorem resourceRequirements62_68_b17 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 17 (j.val + 1)
      (resources68 (resourceSelector68_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_18 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 7
  | 1 => 7
  | 2 => 8
  | 3 => 8
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | 7 => 9
  | 8 => 9
  | 9 => 9
  | _ => 9

private theorem resourceRequirements62_68_b18 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 18 (j.val + 1)
      (resources68 (resourceSelector68_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_19 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 9
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | 7 => 9
  | 8 => 9
  | 9 => 9
  | _ => 10

private theorem resourceRequirements62_68_b19 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 19 (j.val + 1)
      (resources68 (resourceSelector68_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_20 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 9
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | 7 => 9
  | 8 => 10
  | 9 => 10
  | _ => 11

private theorem resourceRequirements62_68_b20 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 20 (j.val + 1)
      (resources68 (resourceSelector68_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_21 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 9
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 10
  | 7 => 10
  | 8 => 11
  | 9 => 11
  | _ => 12

private theorem resourceRequirements62_68_b21 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 21 (j.val + 1)
      (resources68 (resourceSelector68_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68_22 (j : Fin 11) : Fin 13 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 9
  | 3 => 9
  | 4 => 10
  | 5 => 10
  | 6 => 11
  | 7 => 11
  | 8 => 11
  | 9 => 12
  | _ => 12

private theorem resourceRequirements62_68_b22 :
    ∀ j : Fin 11, ResourceRequirements 68 [3, 5, 7, 11] 22 (j.val + 1)
      (resources68 (resourceSelector68_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector68 (b : Fin 23) (j : Fin 11) : Fin 13 :=
  match b.val with
  | 0 => resourceSelector68_0 j
  | 1 => resourceSelector68_1 j
  | 2 => resourceSelector68_2 j
  | 3 => resourceSelector68_3 j
  | 4 => resourceSelector68_4 j
  | 5 => resourceSelector68_5 j
  | 6 => resourceSelector68_6 j
  | 7 => resourceSelector68_7 j
  | 8 => resourceSelector68_8 j
  | 9 => resourceSelector68_9 j
  | 10 => resourceSelector68_10 j
  | 11 => resourceSelector68_11 j
  | 12 => resourceSelector68_12 j
  | 13 => resourceSelector68_13 j
  | 14 => resourceSelector68_14 j
  | 15 => resourceSelector68_15 j
  | 16 => resourceSelector68_16 j
  | 17 => resourceSelector68_17 j
  | 18 => resourceSelector68_18 j
  | 19 => resourceSelector68_19 j
  | 20 => resourceSelector68_20 j
  | 21 => resourceSelector68_21 j
  | _ => resourceSelector68_22 j

theorem finiteCheck62_68 : finiteIntervalCheck 62 68 smallOrder68 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 62) (U := 68) (O := smallOrder68) (ps := [3, 5, 7, 11]) resources68 resourceSelector68
  · intro i
    fin_cases i
    · exact validResource68_0
    · exact validResource68_1
    · exact validResource68_2
    · exact validResource68_3
    · exact validResource68_4
    · exact validResource68_5
    · exact validResource68_6
    · exact validResource68_7
    · exact validResource68_8
    · exact validResource68_9
    · exact validResource68_10
    · exact validResource68_11
    · exact validResource68_12
  · intro b j
    fin_cases b
    · exact resourceRequirements62_68_b0 j
    · exact resourceRequirements62_68_b1 j
    · exact resourceRequirements62_68_b2 j
    · exact resourceRequirements62_68_b3 j
    · exact resourceRequirements62_68_b4 j
    · exact resourceRequirements62_68_b5 j
    · exact resourceRequirements62_68_b6 j
    · exact resourceRequirements62_68_b7 j
    · exact resourceRequirements62_68_b8 j
    · exact resourceRequirements62_68_b9 j
    · exact resourceRequirements62_68_b10 j
    · exact resourceRequirements62_68_b11 j
    · exact resourceRequirements62_68_b12 j
    · exact resourceRequirements62_68_b13 j
    · exact resourceRequirements62_68_b14 j
    · exact resourceRequirements62_68_b15 j
    · exact resourceRequirements62_68_b16 j
    · exact resourceRequirements62_68_b17 j
    · exact resourceRequirements62_68_b18 j
    · exact resourceRequirements62_68_b19 j
    · exact resourceRequirements62_68_b20 j
    · exact resourceRequirements62_68_b21 j
    · exact resourceRequirements62_68_b22 j

theorem exactCertificate62_68 : ExactIntervalCertificate 62 68 smallOrder68 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck62_68
#print axioms smallOrder68_nodup
#print axioms smallOrder68_set
#print axioms finiteCheck62_68
#print axioms exactCertificate62_68
end Erdos883Verified
