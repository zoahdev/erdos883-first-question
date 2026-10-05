import Erdos883SmallCertificateListCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder75 : List ℕ := [1, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 49, 5, 25, 65, 55, 35, 3, 9, 27, 69, 57, 51, 39, 33, 21, 63, 15, 45, 75]
theorem smallOrder75_nodup : smallOrder75.Nodup := by decide +kernel
theorem smallOrder75_set : smallOrder75.toFinset = oddUniverse 75 := by decide +kernel

private def resources75 (i : Fin 15) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨38, 0, 14, true⟩
  | 1 => ⟨30, 0, 15, true⟩
  | 2 => ⟨30, 1, 21, true⟩
  | 3 => ⟨28, 0, 16, true⟩
  | 4 => ⟨25, 0, 21, true⟩
  | 5 => ⟨23, 0, 22, true⟩
  | 6 => ⟨22, 0, 24, true⟩
  | 7 => ⟨20, 0, 27, true⟩
  | 8 => ⟨18, 0, 29, true⟩
  | 9 => ⟨17, 0, 30, true⟩
  | 10 => ⟨16, 0, 31, true⟩
  | 11 => ⟨15, 0, 32, true⟩
  | 12 => ⟨12, 0, 33, true⟩
  | 13 => ⟨11, 0, 34, true⟩
  | _ => ⟨10, 0, 67, false⟩

private theorem validResource75_0 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 0) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_1 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 1) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_2 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 2) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_3 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 3) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_4 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 4) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_5 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 5) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_6 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 6) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_7 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 7) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_8 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 8) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_9 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 9) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_10 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 10) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_11 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 11) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_12 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 12) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_13 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 13) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private theorem validResource75_14 :
    PrefixResourceValid 69 smallOrder75 [3, 5, 7, 11] (resources75 14) := by
  unfold PrefixResourceValid
  apply prefixResourceBound_of_listCheck
  decide +kernel

private def resourceSelector75_0 (j : Fin 12) : Fin 15 :=
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
  | 10 => 0
  | _ => 0

private theorem resourceRequirements69_75_b0 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 0 (j.val + 1)
      (resources75 (resourceSelector75_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_1 (j : Fin 12) : Fin 15 :=
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
  | 10 => 0
  | _ => 0

private theorem resourceRequirements69_75_b1 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 1 (j.val + 1)
      (resources75 (resourceSelector75_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_2 (j : Fin 12) : Fin 15 :=
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
  | 10 => 0
  | _ => 0

private theorem resourceRequirements69_75_b2 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 2 (j.val + 1)
      (resources75 (resourceSelector75_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_3 (j : Fin 12) : Fin 15 :=
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
  | 10 => 1
  | _ => 1

private theorem resourceRequirements69_75_b3 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 3 (j.val + 1)
      (resources75 (resourceSelector75_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_4 (j : Fin 12) : Fin 15 :=
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
  | 10 => 1
  | _ => 2

private theorem resourceRequirements69_75_b4 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 4 (j.val + 1)
      (resources75 (resourceSelector75_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_5 (j : Fin 12) : Fin 15 :=
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
  | 10 => 3
  | _ => 2

private theorem resourceRequirements69_75_b5 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 5 (j.val + 1)
      (resources75 (resourceSelector75_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_6 (j : Fin 12) : Fin 15 :=
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
  | 9 => 3
  | 10 => 2
  | _ => 2

private theorem resourceRequirements69_75_b6 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 6 (j.val + 1)
      (resources75 (resourceSelector75_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_7 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 3
  | 7 => 3
  | 8 => 3
  | 9 => 2
  | 10 => 2
  | _ => 2

private theorem resourceRequirements69_75_b7 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 7 (j.val + 1)
      (resources75 (resourceSelector75_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_8 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 2
  | 10 => 4
  | _ => 4

private theorem resourceRequirements69_75_b8 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 8 (j.val + 1)
      (resources75 (resourceSelector75_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_9 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 4
  | 9 => 4
  | 10 => 4
  | _ => 4

private theorem resourceRequirements69_75_b9 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 9 (j.val + 1)
      (resources75 (resourceSelector75_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_10 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 4
  | 7 => 4
  | 8 => 4
  | 9 => 4
  | 10 => 5
  | _ => 5

private theorem resourceRequirements69_75_b10 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 10 (j.val + 1)
      (resources75 (resourceSelector75_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_11 (j : Fin 12) : Fin 15 :=
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
  | 9 => 5
  | 10 => 6
  | _ => 6

private theorem resourceRequirements69_75_b11 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 11 (j.val + 1)
      (resources75 (resourceSelector75_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_12 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 3
  | 1 => 3
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 5
  | 7 => 5
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | _ => 6

private theorem resourceRequirements69_75_b12 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 12 (j.val + 1)
      (resources75 (resourceSelector75_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_13 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 4
  | 1 => 4
  | 2 => 4
  | 3 => 4
  | 4 => 5
  | 5 => 5
  | 6 => 6
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | 10 => 7
  | _ => 7

private theorem resourceRequirements69_75_b13 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 13 (j.val + 1)
      (resources75 (resourceSelector75_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_14 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 4
  | 1 => 4
  | 2 => 5
  | 3 => 5
  | 4 => 6
  | 5 => 6
  | 6 => 6
  | 7 => 6
  | 8 => 7
  | 9 => 7
  | 10 => 7
  | _ => 7

private theorem resourceRequirements69_75_b14 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 14 (j.val + 1)
      (resources75 (resourceSelector75_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_15 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 6
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | 6 => 7
  | 7 => 7
  | 8 => 7
  | 9 => 7
  | 10 => 8
  | _ => 8

private theorem resourceRequirements69_75_b15 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 15 (j.val + 1)
      (resources75 (resourceSelector75_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_16 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | 3 => 6
  | 4 => 7
  | 5 => 7
  | 6 => 7
  | 7 => 7
  | 8 => 8
  | 9 => 8
  | 10 => 9
  | _ => 9

private theorem resourceRequirements69_75_b16 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 16 (j.val + 1)
      (resources75 (resourceSelector75_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_17 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 7
  | 3 => 7
  | 4 => 7
  | 5 => 7
  | 6 => 8
  | 7 => 8
  | 8 => 9
  | 9 => 9
  | 10 => 10
  | _ => 10

private theorem resourceRequirements69_75_b17 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 17 (j.val + 1)
      (resources75 (resourceSelector75_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_18 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 7
  | 1 => 7
  | 2 => 7
  | 3 => 7
  | 4 => 8
  | 5 => 8
  | 6 => 9
  | 7 => 9
  | 8 => 10
  | 9 => 10
  | 10 => 11
  | _ => 11

private theorem resourceRequirements69_75_b18 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 18 (j.val + 1)
      (resources75 (resourceSelector75_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_19 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 7
  | 1 => 7
  | 2 => 8
  | 3 => 8
  | 4 => 9
  | 5 => 9
  | 6 => 10
  | 7 => 10
  | 8 => 11
  | 9 => 11
  | 10 => 11
  | _ => 11

private theorem resourceRequirements69_75_b19 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 19 (j.val + 1)
      (resources75 (resourceSelector75_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_20 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 9
  | 3 => 9
  | 4 => 10
  | 5 => 10
  | 6 => 11
  | 7 => 11
  | 8 => 11
  | 9 => 11
  | 10 => 11
  | _ => 11

private theorem resourceRequirements69_75_b20 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 20 (j.val + 1)
      (resources75 (resourceSelector75_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_21 (j : Fin 12) : Fin 15 :=
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
  | 9 => 11
  | 10 => 12
  | _ => 12

private theorem resourceRequirements69_75_b21 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 21 (j.val + 1)
      (resources75 (resourceSelector75_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_22 (j : Fin 12) : Fin 15 :=
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
  | 9 => 12
  | 10 => 13
  | _ => 13

private theorem resourceRequirements69_75_b22 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 22 (j.val + 1)
      (resources75 (resourceSelector75_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_23 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 11
  | 1 => 11
  | 2 => 11
  | 3 => 11
  | 4 => 11
  | 5 => 11
  | 6 => 12
  | 7 => 12
  | 8 => 13
  | 9 => 13
  | 10 => 13
  | _ => 14

private theorem resourceRequirements69_75_b23 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 23 (j.val + 1)
      (resources75 (resourceSelector75_23 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75_24 (j : Fin 12) : Fin 15 :=
  match j.val with
  | 0 => 11
  | 1 => 11
  | 2 => 11
  | 3 => 11
  | 4 => 12
  | 5 => 12
  | 6 => 13
  | 7 => 13
  | 8 => 13
  | 9 => 13
  | 10 => 14
  | _ => 14

private theorem resourceRequirements69_75_b24 :
    ∀ j : Fin 12, ResourceRequirements 75 [3, 5, 7, 11] 24 (j.val + 1)
      (resources75 (resourceSelector75_24 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector75 (b : Fin 25) (j : Fin 12) : Fin 15 :=
  match b.val with
  | 0 => resourceSelector75_0 j
  | 1 => resourceSelector75_1 j
  | 2 => resourceSelector75_2 j
  | 3 => resourceSelector75_3 j
  | 4 => resourceSelector75_4 j
  | 5 => resourceSelector75_5 j
  | 6 => resourceSelector75_6 j
  | 7 => resourceSelector75_7 j
  | 8 => resourceSelector75_8 j
  | 9 => resourceSelector75_9 j
  | 10 => resourceSelector75_10 j
  | 11 => resourceSelector75_11 j
  | 12 => resourceSelector75_12 j
  | 13 => resourceSelector75_13 j
  | 14 => resourceSelector75_14 j
  | 15 => resourceSelector75_15 j
  | 16 => resourceSelector75_16 j
  | 17 => resourceSelector75_17 j
  | 18 => resourceSelector75_18 j
  | 19 => resourceSelector75_19 j
  | 20 => resourceSelector75_20 j
  | 21 => resourceSelector75_21 j
  | 22 => resourceSelector75_22 j
  | 23 => resourceSelector75_23 j
  | _ => resourceSelector75_24 j

theorem finiteCheck69_75 : finiteIntervalCheck 69 75 smallOrder75 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 69) (U := 75) (O := smallOrder75) (ps := [3, 5, 7, 11]) resources75 resourceSelector75
  · intro i
    fin_cases i
    · exact validResource75_0
    · exact validResource75_1
    · exact validResource75_2
    · exact validResource75_3
    · exact validResource75_4
    · exact validResource75_5
    · exact validResource75_6
    · exact validResource75_7
    · exact validResource75_8
    · exact validResource75_9
    · exact validResource75_10
    · exact validResource75_11
    · exact validResource75_12
    · exact validResource75_13
    · exact validResource75_14
  · intro b j
    fin_cases b
    · exact resourceRequirements69_75_b0 j
    · exact resourceRequirements69_75_b1 j
    · exact resourceRequirements69_75_b2 j
    · exact resourceRequirements69_75_b3 j
    · exact resourceRequirements69_75_b4 j
    · exact resourceRequirements69_75_b5 j
    · exact resourceRequirements69_75_b6 j
    · exact resourceRequirements69_75_b7 j
    · exact resourceRequirements69_75_b8 j
    · exact resourceRequirements69_75_b9 j
    · exact resourceRequirements69_75_b10 j
    · exact resourceRequirements69_75_b11 j
    · exact resourceRequirements69_75_b12 j
    · exact resourceRequirements69_75_b13 j
    · exact resourceRequirements69_75_b14 j
    · exact resourceRequirements69_75_b15 j
    · exact resourceRequirements69_75_b16 j
    · exact resourceRequirements69_75_b17 j
    · exact resourceRequirements69_75_b18 j
    · exact resourceRequirements69_75_b19 j
    · exact resourceRequirements69_75_b20 j
    · exact resourceRequirements69_75_b21 j
    · exact resourceRequirements69_75_b22 j
    · exact resourceRequirements69_75_b23 j
    · exact resourceRequirements69_75_b24 j

theorem exactCertificate69_75 : ExactIntervalCertificate 69 75 smallOrder75 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck69_75
#print axioms smallOrder75_nodup
#print axioms smallOrder75_set
#print axioms finiteCheck69_75
#print axioms exactCertificate69_75
end Erdos883Verified
