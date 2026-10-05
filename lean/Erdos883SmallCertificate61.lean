import Erdos883SmallCertificateHelpers
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder61 : List ℕ := [1, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 49, 5, 25, 55, 35, 3, 9, 27, 57, 51, 39, 33, 21, 15, 45]
theorem smallOrder61_nodup : smallOrder61.Nodup := by decide +kernel
theorem smallOrder61_set : smallOrder61.toFinset = oddUniverse 61 := by decide +kernel

private def resources61 (i : Fin 13) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨31, 0, 10, true⟩
  | 1 => ⟨26, 0, 11, true⟩
  | 2 => ⟨26, 1, 17, true⟩
  | 3 => ⟨24, 0, 12, true⟩
  | 4 => ⟨21, 0, 17, true⟩
  | 5 => ⟨19, 0, 19, true⟩
  | 6 => ⟨17, 0, 22, true⟩
  | 7 => ⟨15, 0, 24, true⟩
  | 8 => ⟨14, 0, 25, true⟩
  | 9 => ⟨13, 0, 26, true⟩
  | 10 => ⟨11, 0, 27, true⟩
  | 11 => ⟨10, 0, 28, true⟩
  | _ => ⟨8, 0, 54, false⟩

private theorem validResource61_0 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 0) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_1 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 1) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_2 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 2) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_3 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 3) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_4 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 4) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_5 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 5) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_6 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 6) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_7 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 7) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_8 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 8) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_9 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 9) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_10 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 10) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_11 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 11) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource61_12 :
    PrefixResourceValid 56 smallOrder61 [3, 5, 7, 11] (resources61 12) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private def resourceSelector61_0 (j : Fin 10) : Fin 13 :=
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
  | _ => 0

private theorem resourceRequirements56_61_b0 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 0 (j.val + 1)
      (resources61 (resourceSelector61_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_1 (j : Fin 10) : Fin 13 :=
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
  | _ => 1

private theorem resourceRequirements56_61_b1 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 1 (j.val + 1)
      (resources61 (resourceSelector61_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_2 (j : Fin 10) : Fin 13 :=
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
  | _ => 2

private theorem resourceRequirements56_61_b2 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 2 (j.val + 1)
      (resources61 (resourceSelector61_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_3 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 3
  | _ => 2

private theorem resourceRequirements56_61_b3 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 3 (j.val + 1)
      (resources61 (resourceSelector61_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_4 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | _ => 2

private theorem resourceRequirements56_61_b4 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 4 (j.val + 1)
      (resources61 (resourceSelector61_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_5 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 2
  | _ => 2

private theorem resourceRequirements56_61_b5 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 5 (j.val + 1)
      (resources61 (resourceSelector61_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_6 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 2
  | 7 => 2
  | 8 => 4
  | _ => 4

private theorem resourceRequirements56_61_b6 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 6 (j.val + 1)
      (resources61 (resourceSelector61_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_7 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 2
  | 6 => 4
  | 7 => 4
  | 8 => 4
  | _ => 4

private theorem resourceRequirements56_61_b7 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 7 (j.val + 1)
      (resources61 (resourceSelector61_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_8 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | 7 => 4
  | 8 => 5
  | _ => 5

private theorem resourceRequirements56_61_b8 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 8 (j.val + 1)
      (resources61 (resourceSelector61_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_9 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 3
  | 1 => 3
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 5
  | 7 => 5
  | 8 => 5
  | _ => 5

private theorem resourceRequirements56_61_b9 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 9 (j.val + 1)
      (resources61 (resourceSelector61_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_10 (j : Fin 10) : Fin 13 :=
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
  | _ => 6

private theorem resourceRequirements56_61_b10 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 10 (j.val + 1)
      (resources61 (resourceSelector61_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_11 (j : Fin 10) : Fin 13 :=
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
  | _ => 6

private theorem resourceRequirements56_61_b11 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 11 (j.val + 1)
      (resources61 (resourceSelector61_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_12 (j : Fin 10) : Fin 13 :=
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
  | _ => 7

private theorem resourceRequirements56_61_b12 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 12 (j.val + 1)
      (resources61 (resourceSelector61_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_13 (j : Fin 10) : Fin 13 :=
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
  | _ => 8

private theorem resourceRequirements56_61_b13 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 13 (j.val + 1)
      (resources61 (resourceSelector61_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_14 (j : Fin 10) : Fin 13 :=
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
  | _ => 9

private theorem resourceRequirements56_61_b14 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 14 (j.val + 1)
      (resources61 (resourceSelector61_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_15 (j : Fin 10) : Fin 13 :=
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
  | _ => 9

private theorem resourceRequirements56_61_b15 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 15 (j.val + 1)
      (resources61 (resourceSelector61_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_16 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 7
  | 1 => 7
  | 2 => 8
  | 3 => 8
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | 7 => 9
  | 8 => 10
  | _ => 10

private theorem resourceRequirements56_61_b16 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 16 (j.val + 1)
      (resources61 (resourceSelector61_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_17 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 9
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 10
  | 7 => 10
  | 8 => 11
  | _ => 11

private theorem resourceRequirements56_61_b17 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 17 (j.val + 1)
      (resources61 (resourceSelector61_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_18 (j : Fin 10) : Fin 13 :=
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
  | _ => 11

private theorem resourceRequirements56_61_b18 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 18 (j.val + 1)
      (resources61 (resourceSelector61_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_19 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 10
  | 3 => 10
  | 4 => 11
  | 5 => 11
  | 6 => 11
  | 7 => 11
  | 8 => 11
  | _ => 12

private theorem resourceRequirements56_61_b19 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 19 (j.val + 1)
      (resources61 (resourceSelector61_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61_20 (j : Fin 10) : Fin 13 :=
  match j.val with
  | 0 => 10
  | 1 => 10
  | 2 => 11
  | 3 => 11
  | 4 => 11
  | 5 => 11
  | 6 => 11
  | 7 => 11
  | 8 => 12
  | _ => 12

private theorem resourceRequirements56_61_b20 :
    ∀ j : Fin 10, ResourceRequirements 61 [3, 5, 7, 11] 20 (j.val + 1)
      (resources61 (resourceSelector61_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector61 (b : Fin 21) (j : Fin 10) : Fin 13 :=
  match b.val with
  | 0 => resourceSelector61_0 j
  | 1 => resourceSelector61_1 j
  | 2 => resourceSelector61_2 j
  | 3 => resourceSelector61_3 j
  | 4 => resourceSelector61_4 j
  | 5 => resourceSelector61_5 j
  | 6 => resourceSelector61_6 j
  | 7 => resourceSelector61_7 j
  | 8 => resourceSelector61_8 j
  | 9 => resourceSelector61_9 j
  | 10 => resourceSelector61_10 j
  | 11 => resourceSelector61_11 j
  | 12 => resourceSelector61_12 j
  | 13 => resourceSelector61_13 j
  | 14 => resourceSelector61_14 j
  | 15 => resourceSelector61_15 j
  | 16 => resourceSelector61_16 j
  | 17 => resourceSelector61_17 j
  | 18 => resourceSelector61_18 j
  | 19 => resourceSelector61_19 j
  | _ => resourceSelector61_20 j

theorem finiteCheck56_61 : finiteIntervalCheck 56 61 smallOrder61 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 56) (U := 61) (O := smallOrder61) (ps := [3, 5, 7, 11]) resources61 resourceSelector61
  · intro i
    fin_cases i
    · exact validResource61_0
    · exact validResource61_1
    · exact validResource61_2
    · exact validResource61_3
    · exact validResource61_4
    · exact validResource61_5
    · exact validResource61_6
    · exact validResource61_7
    · exact validResource61_8
    · exact validResource61_9
    · exact validResource61_10
    · exact validResource61_11
    · exact validResource61_12
  · intro b j
    fin_cases b
    · exact resourceRequirements56_61_b0 j
    · exact resourceRequirements56_61_b1 j
    · exact resourceRequirements56_61_b2 j
    · exact resourceRequirements56_61_b3 j
    · exact resourceRequirements56_61_b4 j
    · exact resourceRequirements56_61_b5 j
    · exact resourceRequirements56_61_b6 j
    · exact resourceRequirements56_61_b7 j
    · exact resourceRequirements56_61_b8 j
    · exact resourceRequirements56_61_b9 j
    · exact resourceRequirements56_61_b10 j
    · exact resourceRequirements56_61_b11 j
    · exact resourceRequirements56_61_b12 j
    · exact resourceRequirements56_61_b13 j
    · exact resourceRequirements56_61_b14 j
    · exact resourceRequirements56_61_b15 j
    · exact resourceRequirements56_61_b16 j
    · exact resourceRequirements56_61_b17 j
    · exact resourceRequirements56_61_b18 j
    · exact resourceRequirements56_61_b19 j
    · exact resourceRequirements56_61_b20 j

theorem exactCertificate56_61 : ExactIntervalCertificate 56 61 smallOrder61 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck56_61
#print axioms smallOrder61_nodup
#print axioms smallOrder61_set
#print axioms finiteCheck56_61
#print axioms exactCertificate56_61
end Erdos883Verified
