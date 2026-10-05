import Erdos883SmallCertificateFastCount
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder117 : List ℕ := [1, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 49, 5, 25, 91, 77, 115, 95, 85, 65, 55, 35, 3, 9, 27, 81, 111, 93, 87, 69, 57, 51, 39, 117, 33, 99, 21, 63, 15, 45, 75, 105]
theorem smallOrder117_nodup : smallOrder117.Nodup := by decide +kernel
theorem smallOrder117_set : smallOrder117.toFinset = oddUniverse 117 := by decide +kernel

private def resources117 (i : Fin 23) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨59, 0, 19, true⟩
  | 1 => ⟨49, 0, 23, true⟩
  | 2 => ⟨45, 0, 25, true⟩
  | 3 => ⟨43, 0, 26, true⟩
  | 4 => ⟨44, 1, 29, true⟩
  | 5 => ⟨39, 0, 32, true⟩
  | 6 => ⟨36, 0, 33, true⟩
  | 7 => ⟨38, 2, 34, true⟩
  | 8 => ⟨37, 2, 35, true⟩
  | 9 => ⟨34, 0, 34, true⟩
  | 10 => ⟨36, 2, 37, true⟩
  | 11 => ⟨33, 0, 36, true⟩
  | 12 => ⟨31, 0, 39, true⟩
  | 13 => ⟨29, 0, 41, true⟩
  | 14 => ⟨27, 0, 42, true⟩
  | 15 => ⟨26, 0, 43, true⟩
  | 16 => ⟨25, 0, 44, true⟩
  | 17 => ⟨24, 0, 45, true⟩
  | 18 => ⟨23, 0, 46, true⟩
  | 19 => ⟨22, 0, 47, true⟩
  | 20 => ⟨21, 0, 52, true⟩
  | 21 => ⟨16, 0, 53, true⟩
  | _ => ⟨15, 0, 57, true⟩

private theorem validResource117_0 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 0) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_1 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 1) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_2 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 2) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_3 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 3) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_4 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 4) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_5 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 5) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_6 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 6) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_7 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 7) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_8 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 8) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_9 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 9) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_10 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 10) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_11 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 11) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_12 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 12) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_13 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 13) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_14 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 14) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_15 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 15) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_16 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 16) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_17 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 17) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_18 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 18) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_19 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 19) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_20 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 20) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_21 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 21) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource117_22 :
    PrefixResourceValid 117 smallOrder117 [3, 5, 7, 11] (resources117 22) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private def resourceSelector117_0 (j : Fin 19) : Fin 23 :=
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
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | _ => 0

private theorem resourceRequirements117_117_b0 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 0 (j.val + 1)
      (resources117 (resourceSelector117_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_1 (j : Fin 19) : Fin 23 :=
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
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | _ => 1

private theorem resourceRequirements117_117_b1 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 1 (j.val + 1)
      (resources117 (resourceSelector117_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_2 (j : Fin 19) : Fin 23 :=
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
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 1
  | 17 => 1
  | _ => 1

private theorem resourceRequirements117_117_b2 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 2 (j.val + 1)
      (resources117 (resourceSelector117_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_3 (j : Fin 19) : Fin 23 :=
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
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 1
  | 15 => 1
  | 16 => 1
  | 17 => 1
  | _ => 1

private theorem resourceRequirements117_117_b3 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 3 (j.val + 1)
      (resources117 (resourceSelector117_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_4 (j : Fin 19) : Fin 23 :=
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
  | 11 => 0
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 1
  | 17 => 1
  | _ => 1

private theorem resourceRequirements117_117_b4 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 4 (j.val + 1)
      (resources117 (resourceSelector117_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_5 (j : Fin 19) : Fin 23 :=
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
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 1
  | 17 => 1
  | _ => 2

private theorem resourceRequirements117_117_b5 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 5 (j.val + 1)
      (resources117 (resourceSelector117_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_6 (j : Fin 19) : Fin 23 :=
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
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 2
  | 17 => 2
  | _ => 2

private theorem resourceRequirements117_117_b6 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 6 (j.val + 1)
      (resources117 (resourceSelector117_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_7 (j : Fin 19) : Fin 23 :=
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
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 2
  | 15 => 2
  | 16 => 2
  | 17 => 2
  | _ => 3

private theorem resourceRequirements117_117_b7 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 7 (j.val + 1)
      (resources117 (resourceSelector117_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_8 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 2
  | 16 => 3
  | 17 => 3
  | _ => 4

private theorem resourceRequirements117_117_b8 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 8 (j.val + 1)
      (resources117 (resourceSelector117_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_9 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 2
  | 11 => 2
  | 12 => 2
  | 13 => 2
  | 14 => 3
  | 15 => 3
  | 16 => 3
  | 17 => 4
  | _ => 4

private theorem resourceRequirements117_117_b9 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 9 (j.val + 1)
      (resources117 (resourceSelector117_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_10 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 3
  | 13 => 3
  | 14 => 3
  | 15 => 3
  | 16 => 4
  | 17 => 4
  | _ => 4

private theorem resourceRequirements117_117_b10 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 10 (j.val + 1)
      (resources117 (resourceSelector117_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_11 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 2
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 3
  | 14 => 3
  | 15 => 4
  | 16 => 4
  | 17 => 4
  | _ => 5

private theorem resourceRequirements117_117_b11 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 11 (j.val + 1)
      (resources117 (resourceSelector117_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_12 (j : Fin 19) : Fin 23 :=
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
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 3
  | 14 => 4
  | 15 => 4
  | 16 => 5
  | 17 => 5
  | _ => 5

private theorem resourceRequirements117_117_b12 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 12 (j.val + 1)
      (resources117 (resourceSelector117_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_13 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 3
  | 8 => 3
  | 9 => 3
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 4
  | 14 => 5
  | 15 => 5
  | 16 => 5
  | 17 => 5
  | _ => 5

private theorem resourceRequirements117_117_b13 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 13 (j.val + 1)
      (resources117 (resourceSelector117_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_14 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 3
  | 9 => 3
  | 10 => 3
  | 11 => 3
  | 12 => 5
  | 13 => 5
  | 14 => 5
  | 15 => 5
  | 16 => 5
  | 17 => 5
  | _ => 6

private theorem resourceRequirements117_117_b14 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 14 (j.val + 1)
      (resources117 (resourceSelector117_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_15 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 3
  | 9 => 3
  | 10 => 5
  | 11 => 5
  | 12 => 5
  | 13 => 5
  | 14 => 5
  | 15 => 5
  | 16 => 6
  | 17 => 6
  | _ => 7

private theorem resourceRequirements117_117_b15 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 15 (j.val + 1)
      (resources117 (resourceSelector117_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_16 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 5
  | 9 => 5
  | 10 => 5
  | 11 => 5
  | 12 => 5
  | 13 => 5
  | 14 => 6
  | 15 => 6
  | 16 => 6
  | 17 => 8
  | _ => 8

private theorem resourceRequirements117_117_b16 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 16 (j.val + 1)
      (resources117 (resourceSelector117_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_17 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 5
  | 7 => 5
  | 8 => 5
  | 9 => 5
  | 10 => 5
  | 11 => 5
  | 12 => 6
  | 13 => 6
  | 14 => 6
  | 15 => 6
  | 16 => 9
  | 17 => 10
  | _ => 11

private theorem resourceRequirements117_117_b17 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 17 (j.val + 1)
      (resources117 (resourceSelector117_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_18 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | 7 => 5
  | 8 => 5
  | 9 => 5
  | 10 => 6
  | 11 => 6
  | 12 => 6
  | 13 => 6
  | 14 => 9
  | 15 => 9
  | 16 => 11
  | 17 => 11
  | _ => 10

private theorem resourceRequirements117_117_b18 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 18 (j.val + 1)
      (resources117 (resourceSelector117_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_19 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 3
  | 1 => 3
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | 7 => 5
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | 11 => 6
  | 12 => 9
  | 13 => 9
  | 14 => 11
  | 15 => 11
  | 16 => 11
  | 17 => 10
  | _ => 12

private theorem resourceRequirements117_117_b19 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 19 (j.val + 1)
      (resources117 (resourceSelector117_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_20 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 6
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | 10 => 9
  | 11 => 9
  | 12 => 11
  | 13 => 11
  | 14 => 11
  | 15 => 11
  | 16 => 12
  | 17 => 12
  | _ => 12

private theorem resourceRequirements117_117_b20 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 20 (j.val + 1)
      (resources117 (resourceSelector117_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_21 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 6
  | 5 => 6
  | 6 => 6
  | 7 => 6
  | 8 => 9
  | 9 => 9
  | 10 => 11
  | 11 => 11
  | 12 => 11
  | 13 => 11
  | 14 => 12
  | 15 => 12
  | 16 => 12
  | 17 => 12
  | _ => 13

private theorem resourceRequirements117_117_b21 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 21 (j.val + 1)
      (resources117 (resourceSelector117_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_22 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 6
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | 6 => 9
  | 7 => 9
  | 8 => 11
  | 9 => 11
  | 10 => 11
  | 11 => 11
  | 12 => 12
  | 13 => 12
  | 14 => 12
  | 15 => 12
  | 16 => 13
  | 17 => 13
  | _ => 13

private theorem resourceRequirements117_117_b22 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 22 (j.val + 1)
      (resources117 (resourceSelector117_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_23 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | 3 => 6
  | 4 => 9
  | 5 => 9
  | 6 => 11
  | 7 => 11
  | 8 => 11
  | 9 => 11
  | 10 => 12
  | 11 => 12
  | 12 => 12
  | 13 => 12
  | 14 => 13
  | 15 => 13
  | 16 => 13
  | 17 => 13
  | _ => 14

private theorem resourceRequirements117_117_b23 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 23 (j.val + 1)
      (resources117 (resourceSelector117_23 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_24 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 9
  | 3 => 9
  | 4 => 11
  | 5 => 11
  | 6 => 11
  | 7 => 11
  | 8 => 12
  | 9 => 12
  | 10 => 12
  | 11 => 12
  | 12 => 13
  | 13 => 13
  | 14 => 13
  | 15 => 13
  | 16 => 14
  | 17 => 14
  | _ => 15

private theorem resourceRequirements117_117_b24 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 24 (j.val + 1)
      (resources117 (resourceSelector117_24 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_25 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 11
  | 3 => 11
  | 4 => 11
  | 5 => 11
  | 6 => 12
  | 7 => 12
  | 8 => 12
  | 9 => 12
  | 10 => 13
  | 11 => 13
  | 12 => 13
  | 13 => 13
  | 14 => 14
  | 15 => 14
  | 16 => 15
  | 17 => 15
  | _ => 16

private theorem resourceRequirements117_117_b25 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 25 (j.val + 1)
      (resources117 (resourceSelector117_25 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_26 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 11
  | 1 => 11
  | 2 => 11
  | 3 => 11
  | 4 => 12
  | 5 => 12
  | 6 => 12
  | 7 => 12
  | 8 => 13
  | 9 => 13
  | 10 => 13
  | 11 => 13
  | 12 => 14
  | 13 => 14
  | 14 => 15
  | 15 => 15
  | 16 => 16
  | 17 => 16
  | _ => 17

private theorem resourceRequirements117_117_b26 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 26 (j.val + 1)
      (resources117 (resourceSelector117_26 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_27 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 11
  | 1 => 11
  | 2 => 12
  | 3 => 12
  | 4 => 12
  | 5 => 12
  | 6 => 13
  | 7 => 13
  | 8 => 13
  | 9 => 13
  | 10 => 14
  | 11 => 14
  | 12 => 15
  | 13 => 15
  | 14 => 16
  | 15 => 16
  | 16 => 17
  | 17 => 17
  | _ => 18

private theorem resourceRequirements117_117_b27 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 27 (j.val + 1)
      (resources117 (resourceSelector117_27 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_28 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 12
  | 1 => 12
  | 2 => 12
  | 3 => 12
  | 4 => 13
  | 5 => 13
  | 6 => 13
  | 7 => 13
  | 8 => 14
  | 9 => 14
  | 10 => 15
  | 11 => 15
  | 12 => 16
  | 13 => 16
  | 14 => 17
  | 15 => 17
  | 16 => 18
  | 17 => 18
  | _ => 19

private theorem resourceRequirements117_117_b28 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 28 (j.val + 1)
      (resources117 (resourceSelector117_28 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_29 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 12
  | 1 => 12
  | 2 => 13
  | 3 => 13
  | 4 => 13
  | 5 => 13
  | 6 => 14
  | 7 => 14
  | 8 => 15
  | 9 => 15
  | 10 => 16
  | 11 => 16
  | 12 => 17
  | 13 => 17
  | 14 => 18
  | 15 => 18
  | 16 => 19
  | 17 => 19
  | _ => 20

private theorem resourceRequirements117_117_b29 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 29 (j.val + 1)
      (resources117 (resourceSelector117_29 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_30 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 13
  | 1 => 13
  | 2 => 13
  | 3 => 13
  | 4 => 14
  | 5 => 14
  | 6 => 15
  | 7 => 15
  | 8 => 16
  | 9 => 16
  | 10 => 17
  | 11 => 17
  | 12 => 18
  | 13 => 18
  | 14 => 19
  | 15 => 19
  | 16 => 20
  | 17 => 20
  | _ => 20

private theorem resourceRequirements117_117_b30 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 30 (j.val + 1)
      (resources117 (resourceSelector117_30 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_31 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 13
  | 1 => 13
  | 2 => 14
  | 3 => 14
  | 4 => 15
  | 5 => 15
  | 6 => 16
  | 7 => 16
  | 8 => 17
  | 9 => 17
  | 10 => 18
  | 11 => 18
  | 12 => 19
  | 13 => 19
  | 14 => 20
  | 15 => 20
  | 16 => 20
  | 17 => 20
  | _ => 20

private theorem resourceRequirements117_117_b31 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 31 (j.val + 1)
      (resources117 (resourceSelector117_31 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_32 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 14
  | 1 => 14
  | 2 => 15
  | 3 => 15
  | 4 => 16
  | 5 => 16
  | 6 => 17
  | 7 => 17
  | 8 => 18
  | 9 => 18
  | 10 => 19
  | 11 => 19
  | 12 => 20
  | 13 => 20
  | 14 => 20
  | 15 => 20
  | 16 => 20
  | 17 => 20
  | _ => 20

private theorem resourceRequirements117_117_b32 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 32 (j.val + 1)
      (resources117 (resourceSelector117_32 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_33 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 15
  | 1 => 15
  | 2 => 16
  | 3 => 16
  | 4 => 17
  | 5 => 17
  | 6 => 18
  | 7 => 18
  | 8 => 19
  | 9 => 19
  | 10 => 20
  | 11 => 20
  | 12 => 20
  | 13 => 20
  | 14 => 20
  | 15 => 20
  | 16 => 20
  | 17 => 20
  | _ => 20

private theorem resourceRequirements117_117_b33 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 33 (j.val + 1)
      (resources117 (resourceSelector117_33 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_34 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 16
  | 1 => 16
  | 2 => 17
  | 3 => 17
  | 4 => 18
  | 5 => 18
  | 6 => 19
  | 7 => 19
  | 8 => 20
  | 9 => 20
  | 10 => 20
  | 11 => 20
  | 12 => 20
  | 13 => 20
  | 14 => 20
  | 15 => 20
  | 16 => 20
  | 17 => 20
  | _ => 21

private theorem resourceRequirements117_117_b34 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 34 (j.val + 1)
      (resources117 (resourceSelector117_34 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_35 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 17
  | 1 => 17
  | 2 => 18
  | 3 => 18
  | 4 => 19
  | 5 => 19
  | 6 => 20
  | 7 => 20
  | 8 => 20
  | 9 => 20
  | 10 => 20
  | 11 => 20
  | 12 => 20
  | 13 => 20
  | 14 => 20
  | 15 => 20
  | 16 => 21
  | 17 => 21
  | _ => 22

private theorem resourceRequirements117_117_b35 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 35 (j.val + 1)
      (resources117 (resourceSelector117_35 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_36 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 18
  | 1 => 18
  | 2 => 19
  | 3 => 19
  | 4 => 20
  | 5 => 20
  | 6 => 20
  | 7 => 20
  | 8 => 20
  | 9 => 20
  | 10 => 20
  | 11 => 20
  | 12 => 20
  | 13 => 20
  | 14 => 21
  | 15 => 21
  | 16 => 22
  | 17 => 22
  | _ => 22

private theorem resourceRequirements117_117_b36 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 36 (j.val + 1)
      (resources117 (resourceSelector117_36 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_37 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 19
  | 1 => 19
  | 2 => 20
  | 3 => 20
  | 4 => 20
  | 5 => 20
  | 6 => 20
  | 7 => 20
  | 8 => 20
  | 9 => 20
  | 10 => 20
  | 11 => 20
  | 12 => 21
  | 13 => 21
  | 14 => 22
  | 15 => 22
  | 16 => 22
  | 17 => 22
  | _ => 22

private theorem resourceRequirements117_117_b37 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 37 (j.val + 1)
      (resources117 (resourceSelector117_37 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117_38 (j : Fin 19) : Fin 23 :=
  match j.val with
  | 0 => 20
  | 1 => 20
  | 2 => 20
  | 3 => 20
  | 4 => 20
  | 5 => 20
  | 6 => 20
  | 7 => 20
  | 8 => 20
  | 9 => 20
  | 10 => 21
  | 11 => 21
  | 12 => 22
  | 13 => 22
  | 14 => 22
  | 15 => 22
  | 16 => 22
  | 17 => 22
  | _ => 22

private theorem resourceRequirements117_117_b38 :
    ∀ j : Fin 19, ResourceRequirements 117 [3, 5, 7, 11] 38 (j.val + 1)
      (resources117 (resourceSelector117_38 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector117 (b : Fin 39) (j : Fin 19) : Fin 23 :=
  match b.val with
  | 0 => resourceSelector117_0 j
  | 1 => resourceSelector117_1 j
  | 2 => resourceSelector117_2 j
  | 3 => resourceSelector117_3 j
  | 4 => resourceSelector117_4 j
  | 5 => resourceSelector117_5 j
  | 6 => resourceSelector117_6 j
  | 7 => resourceSelector117_7 j
  | 8 => resourceSelector117_8 j
  | 9 => resourceSelector117_9 j
  | 10 => resourceSelector117_10 j
  | 11 => resourceSelector117_11 j
  | 12 => resourceSelector117_12 j
  | 13 => resourceSelector117_13 j
  | 14 => resourceSelector117_14 j
  | 15 => resourceSelector117_15 j
  | 16 => resourceSelector117_16 j
  | 17 => resourceSelector117_17 j
  | 18 => resourceSelector117_18 j
  | 19 => resourceSelector117_19 j
  | 20 => resourceSelector117_20 j
  | 21 => resourceSelector117_21 j
  | 22 => resourceSelector117_22 j
  | 23 => resourceSelector117_23 j
  | 24 => resourceSelector117_24 j
  | 25 => resourceSelector117_25 j
  | 26 => resourceSelector117_26 j
  | 27 => resourceSelector117_27 j
  | 28 => resourceSelector117_28 j
  | 29 => resourceSelector117_29 j
  | 30 => resourceSelector117_30 j
  | 31 => resourceSelector117_31 j
  | 32 => resourceSelector117_32 j
  | 33 => resourceSelector117_33 j
  | 34 => resourceSelector117_34 j
  | 35 => resourceSelector117_35 j
  | 36 => resourceSelector117_36 j
  | 37 => resourceSelector117_37 j
  | _ => resourceSelector117_38 j

theorem finiteCheck117_117 : finiteIntervalCheck 117 117 smallOrder117 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 117) (U := 117) (O := smallOrder117) (ps := [3, 5, 7, 11]) resources117 resourceSelector117
  · intro i
    fin_cases i
    · exact validResource117_0
    · exact validResource117_1
    · exact validResource117_2
    · exact validResource117_3
    · exact validResource117_4
    · exact validResource117_5
    · exact validResource117_6
    · exact validResource117_7
    · exact validResource117_8
    · exact validResource117_9
    · exact validResource117_10
    · exact validResource117_11
    · exact validResource117_12
    · exact validResource117_13
    · exact validResource117_14
    · exact validResource117_15
    · exact validResource117_16
    · exact validResource117_17
    · exact validResource117_18
    · exact validResource117_19
    · exact validResource117_20
    · exact validResource117_21
    · exact validResource117_22
  · intro b j
    fin_cases b
    · exact resourceRequirements117_117_b0 j
    · exact resourceRequirements117_117_b1 j
    · exact resourceRequirements117_117_b2 j
    · exact resourceRequirements117_117_b3 j
    · exact resourceRequirements117_117_b4 j
    · exact resourceRequirements117_117_b5 j
    · exact resourceRequirements117_117_b6 j
    · exact resourceRequirements117_117_b7 j
    · exact resourceRequirements117_117_b8 j
    · exact resourceRequirements117_117_b9 j
    · exact resourceRequirements117_117_b10 j
    · exact resourceRequirements117_117_b11 j
    · exact resourceRequirements117_117_b12 j
    · exact resourceRequirements117_117_b13 j
    · exact resourceRequirements117_117_b14 j
    · exact resourceRequirements117_117_b15 j
    · exact resourceRequirements117_117_b16 j
    · exact resourceRequirements117_117_b17 j
    · exact resourceRequirements117_117_b18 j
    · exact resourceRequirements117_117_b19 j
    · exact resourceRequirements117_117_b20 j
    · exact resourceRequirements117_117_b21 j
    · exact resourceRequirements117_117_b22 j
    · exact resourceRequirements117_117_b23 j
    · exact resourceRequirements117_117_b24 j
    · exact resourceRequirements117_117_b25 j
    · exact resourceRequirements117_117_b26 j
    · exact resourceRequirements117_117_b27 j
    · exact resourceRequirements117_117_b28 j
    · exact resourceRequirements117_117_b29 j
    · exact resourceRequirements117_117_b30 j
    · exact resourceRequirements117_117_b31 j
    · exact resourceRequirements117_117_b32 j
    · exact resourceRequirements117_117_b33 j
    · exact resourceRequirements117_117_b34 j
    · exact resourceRequirements117_117_b35 j
    · exact resourceRequirements117_117_b36 j
    · exact resourceRequirements117_117_b37 j
    · exact resourceRequirements117_117_b38 j

theorem exactCertificate117_117 : ExactIntervalCertificate 117 117 smallOrder117 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck117_117
#print axioms smallOrder117_nodup
#print axioms smallOrder117_set
#print axioms finiteCheck117_117
#print axioms exactCertificate117_117
end Erdos883Verified
