import Erdos883SmallCertificateFastCount
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder116 : List ℕ := [1, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 49, 5, 25, 91, 77, 115, 95, 85, 65, 55, 35, 3, 9, 27, 81, 111, 93, 87, 69, 57, 51, 39, 33, 99, 21, 63, 15, 45, 75, 105]
theorem smallOrder116_nodup : smallOrder116.Nodup := by decide +kernel
theorem smallOrder116_set : smallOrder116.toFinset = oddUniverse 116 := by decide +kernel

private def resources116 (i : Fin 20) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨58, 0, 18, true⟩
  | 1 => ⟨49, 0, 22, true⟩
  | 2 => ⟨45, 0, 24, true⟩
  | 3 => ⟨43, 0, 26, true⟩
  | 4 => ⟨43, 1, 28, true⟩
  | 5 => ⟨39, 0, 31, true⟩
  | 6 => ⟨36, 0, 33, true⟩
  | 7 => ⟨34, 0, 34, true⟩
  | 8 => ⟨33, 0, 36, true⟩
  | 9 => ⟨31, 0, 38, true⟩
  | 10 => ⟨29, 0, 40, true⟩
  | 11 => ⟨27, 0, 41, true⟩
  | 12 => ⟨26, 0, 42, true⟩
  | 13 => ⟨25, 0, 43, true⟩
  | 14 => ⟨24, 0, 44, true⟩
  | 15 => ⟨23, 0, 45, true⟩
  | 16 => ⟨22, 0, 46, true⟩
  | 17 => ⟨21, 0, 51, true⟩
  | 18 => ⟨16, 0, 52, true⟩
  | _ => ⟨15, 0, 57, true⟩

private theorem validResource116_0 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 0) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_1 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 1) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_2 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 2) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_3 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 3) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_4 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 4) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_5 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 5) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_6 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 6) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_7 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 7) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_8 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 8) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_9 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 9) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_10 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 10) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_11 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 11) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_12 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 12) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_13 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 13) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_14 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 14) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_15 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 15) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_16 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 16) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_17 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 17) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_18 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 18) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private theorem validResource116_19 :
    PrefixResourceValid 116 smallOrder116 [3, 5, 7, 11] (resources116 19) := by
  apply prefixResourceValid_of_triangularCheck
  decide +kernel

private def resourceSelector116_0 (j : Fin 19) : Fin 20 :=
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

private theorem resourceRequirements116_116_b0 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 0 (j.val + 1)
      (resources116 (resourceSelector116_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_1 (j : Fin 19) : Fin 20 :=
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

private theorem resourceRequirements116_116_b1 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 1 (j.val + 1)
      (resources116 (resourceSelector116_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_2 (j : Fin 19) : Fin 20 :=
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

private theorem resourceRequirements116_116_b2 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 2 (j.val + 1)
      (resources116 (resourceSelector116_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_3 (j : Fin 19) : Fin 20 :=
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

private theorem resourceRequirements116_116_b3 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 3 (j.val + 1)
      (resources116 (resourceSelector116_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_4 (j : Fin 19) : Fin 20 :=
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

private theorem resourceRequirements116_116_b4 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 4 (j.val + 1)
      (resources116 (resourceSelector116_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_5 (j : Fin 19) : Fin 20 :=
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

private theorem resourceRequirements116_116_b5 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 5 (j.val + 1)
      (resources116 (resourceSelector116_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_6 (j : Fin 19) : Fin 20 :=
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

private theorem resourceRequirements116_116_b6 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 6 (j.val + 1)
      (resources116 (resourceSelector116_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_7 (j : Fin 19) : Fin 20 :=
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
  | _ => 3

private theorem resourceRequirements116_116_b7 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 7 (j.val + 1)
      (resources116 (resourceSelector116_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_8 (j : Fin 19) : Fin 20 :=
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
  | 17 => 3
  | _ => 4

private theorem resourceRequirements116_116_b8 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 8 (j.val + 1)
      (resources116 (resourceSelector116_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_9 (j : Fin 19) : Fin 20 :=
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
  | 16 => 3
  | 17 => 4
  | _ => 4

private theorem resourceRequirements116_116_b9 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 9 (j.val + 1)
      (resources116 (resourceSelector116_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_10 (j : Fin 19) : Fin 20 :=
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
  | 15 => 3
  | 16 => 4
  | 17 => 4
  | _ => 5

private theorem resourceRequirements116_116_b10 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 10 (j.val + 1)
      (resources116 (resourceSelector116_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_11 (j : Fin 19) : Fin 20 :=
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
  | 14 => 3
  | 15 => 4
  | 16 => 5
  | 17 => 5
  | _ => 5

private theorem resourceRequirements116_116_b11 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 11 (j.val + 1)
      (resources116 (resourceSelector116_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_12 (j : Fin 19) : Fin 20 :=
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
  | 13 => 3
  | 14 => 5
  | 15 => 5
  | 16 => 5
  | 17 => 5
  | _ => 5

private theorem resourceRequirements116_116_b12 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 12 (j.val + 1)
      (resources116 (resourceSelector116_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_13 (j : Fin 19) : Fin 20 :=
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

private theorem resourceRequirements116_116_b13 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 13 (j.val + 1)
      (resources116 (resourceSelector116_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_14 (j : Fin 19) : Fin 20 :=
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
  | _ => 6

private theorem resourceRequirements116_116_b14 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 14 (j.val + 1)
      (resources116 (resourceSelector116_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_15 (j : Fin 19) : Fin 20 :=
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
  | 17 => 6
  | _ => 7

private theorem resourceRequirements116_116_b15 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 15 (j.val + 1)
      (resources116 (resourceSelector116_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_16 (j : Fin 19) : Fin 20 :=
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
  | 16 => 7
  | 17 => 7
  | _ => 8

private theorem resourceRequirements116_116_b16 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 16 (j.val + 1)
      (resources116 (resourceSelector116_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_17 (j : Fin 19) : Fin 20 :=
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
  | 14 => 7
  | 15 => 7
  | 16 => 8
  | 17 => 8
  | _ => 8

private theorem resourceRequirements116_116_b17 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 17 (j.val + 1)
      (resources116 (resourceSelector116_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_18 (j : Fin 19) : Fin 20 :=
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
  | 12 => 7
  | 13 => 7
  | 14 => 8
  | 15 => 8
  | 16 => 8
  | 17 => 8
  | _ => 9

private theorem resourceRequirements116_116_b18 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 18 (j.val + 1)
      (resources116 (resourceSelector116_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_19 (j : Fin 19) : Fin 20 :=
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
  | 10 => 7
  | 11 => 7
  | 12 => 8
  | 13 => 8
  | 14 => 8
  | 15 => 8
  | 16 => 9
  | 17 => 9
  | _ => 9

private theorem resourceRequirements116_116_b19 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 19 (j.val + 1)
      (resources116 (resourceSelector116_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_20 (j : Fin 19) : Fin 20 :=
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
  | 10 => 8
  | 11 => 8
  | 12 => 8
  | 13 => 8
  | 14 => 9
  | 15 => 9
  | 16 => 9
  | 17 => 9
  | _ => 10

private theorem resourceRequirements116_116_b20 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 20 (j.val + 1)
      (resources116 (resourceSelector116_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_21 (j : Fin 19) : Fin 20 :=
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
  | 10 => 8
  | 11 => 8
  | 12 => 9
  | 13 => 9
  | 14 => 9
  | 15 => 9
  | 16 => 10
  | 17 => 10
  | _ => 10

private theorem resourceRequirements116_116_b21 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 21 (j.val + 1)
      (resources116 (resourceSelector116_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_22 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | 3 => 6
  | 4 => 7
  | 5 => 7
  | 6 => 8
  | 7 => 8
  | 8 => 8
  | 9 => 8
  | 10 => 9
  | 11 => 9
  | 12 => 9
  | 13 => 9
  | 14 => 10
  | 15 => 10
  | 16 => 10
  | 17 => 10
  | _ => 11

private theorem resourceRequirements116_116_b22 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 22 (j.val + 1)
      (resources116 (resourceSelector116_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_23 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 7
  | 3 => 7
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | 7 => 8
  | 8 => 9
  | 9 => 9
  | 10 => 9
  | 11 => 9
  | 12 => 10
  | 13 => 10
  | 14 => 10
  | 15 => 10
  | 16 => 11
  | 17 => 11
  | _ => 12

private theorem resourceRequirements116_116_b23 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 23 (j.val + 1)
      (resources116 (resourceSelector116_23 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_24 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 7
  | 1 => 7
  | 2 => 8
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 9
  | 7 => 9
  | 8 => 9
  | 9 => 9
  | 10 => 10
  | 11 => 10
  | 12 => 10
  | 13 => 10
  | 14 => 11
  | 15 => 11
  | 16 => 12
  | 17 => 12
  | _ => 13

private theorem resourceRequirements116_116_b24 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 24 (j.val + 1)
      (resources116 (resourceSelector116_24 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_25 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 8
  | 3 => 8
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | 7 => 9
  | 8 => 10
  | 9 => 10
  | 10 => 10
  | 11 => 10
  | 12 => 11
  | 13 => 11
  | 14 => 12
  | 15 => 12
  | 16 => 13
  | 17 => 13
  | _ => 14

private theorem resourceRequirements116_116_b25 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 25 (j.val + 1)
      (resources116 (resourceSelector116_25 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_26 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 9
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 10
  | 7 => 10
  | 8 => 10
  | 9 => 10
  | 10 => 11
  | 11 => 11
  | 12 => 12
  | 13 => 12
  | 14 => 13
  | 15 => 13
  | 16 => 14
  | 17 => 14
  | _ => 15

private theorem resourceRequirements116_116_b26 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 26 (j.val + 1)
      (resources116 (resourceSelector116_26 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_27 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 9
  | 3 => 9
  | 4 => 10
  | 5 => 10
  | 6 => 10
  | 7 => 10
  | 8 => 11
  | 9 => 11
  | 10 => 12
  | 11 => 12
  | 12 => 13
  | 13 => 13
  | 14 => 14
  | 15 => 14
  | 16 => 15
  | 17 => 15
  | _ => 16

private theorem resourceRequirements116_116_b27 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 27 (j.val + 1)
      (resources116 (resourceSelector116_27 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_28 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 10
  | 3 => 10
  | 4 => 10
  | 5 => 10
  | 6 => 11
  | 7 => 11
  | 8 => 12
  | 9 => 12
  | 10 => 13
  | 11 => 13
  | 12 => 14
  | 13 => 14
  | 14 => 15
  | 15 => 15
  | 16 => 16
  | 17 => 16
  | _ => 17

private theorem resourceRequirements116_116_b28 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 28 (j.val + 1)
      (resources116 (resourceSelector116_28 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_29 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 10
  | 1 => 10
  | 2 => 10
  | 3 => 10
  | 4 => 11
  | 5 => 11
  | 6 => 12
  | 7 => 12
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
  | _ => 17

private theorem resourceRequirements116_116_b29 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 29 (j.val + 1)
      (resources116 (resourceSelector116_29 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_30 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 10
  | 1 => 10
  | 2 => 11
  | 3 => 11
  | 4 => 12
  | 5 => 12
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
  | 16 => 17
  | 17 => 17
  | _ => 17

private theorem resourceRequirements116_116_b30 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 30 (j.val + 1)
      (resources116 (resourceSelector116_30 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_31 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 11
  | 1 => 11
  | 2 => 12
  | 3 => 12
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
  | 14 => 17
  | 15 => 17
  | 16 => 17
  | 17 => 17
  | _ => 17

private theorem resourceRequirements116_116_b31 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 31 (j.val + 1)
      (resources116 (resourceSelector116_31 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_32 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 12
  | 1 => 12
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
  | 12 => 17
  | 13 => 17
  | 14 => 17
  | 15 => 17
  | 16 => 17
  | 17 => 17
  | _ => 17

private theorem resourceRequirements116_116_b32 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 32 (j.val + 1)
      (resources116 (resourceSelector116_32 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_33 (j : Fin 19) : Fin 20 :=
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
  | 10 => 17
  | 11 => 17
  | 12 => 17
  | 13 => 17
  | 14 => 17
  | 15 => 17
  | 16 => 17
  | 17 => 17
  | _ => 18

private theorem resourceRequirements116_116_b33 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 33 (j.val + 1)
      (resources116 (resourceSelector116_33 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_34 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 14
  | 1 => 14
  | 2 => 15
  | 3 => 15
  | 4 => 16
  | 5 => 16
  | 6 => 17
  | 7 => 17
  | 8 => 17
  | 9 => 17
  | 10 => 17
  | 11 => 17
  | 12 => 17
  | 13 => 17
  | 14 => 17
  | 15 => 17
  | 16 => 18
  | 17 => 18
  | _ => 19

private theorem resourceRequirements116_116_b34 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 34 (j.val + 1)
      (resources116 (resourceSelector116_34 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_35 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 15
  | 1 => 15
  | 2 => 16
  | 3 => 16
  | 4 => 17
  | 5 => 17
  | 6 => 17
  | 7 => 17
  | 8 => 17
  | 9 => 17
  | 10 => 17
  | 11 => 17
  | 12 => 17
  | 13 => 17
  | 14 => 18
  | 15 => 18
  | 16 => 19
  | 17 => 19
  | _ => 19

private theorem resourceRequirements116_116_b35 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 35 (j.val + 1)
      (resources116 (resourceSelector116_35 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_36 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 16
  | 1 => 16
  | 2 => 17
  | 3 => 17
  | 4 => 17
  | 5 => 17
  | 6 => 17
  | 7 => 17
  | 8 => 17
  | 9 => 17
  | 10 => 17
  | 11 => 17
  | 12 => 18
  | 13 => 18
  | 14 => 19
  | 15 => 19
  | 16 => 19
  | 17 => 19
  | _ => 19

private theorem resourceRequirements116_116_b36 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 36 (j.val + 1)
      (resources116 (resourceSelector116_36 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_37 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 17
  | 1 => 17
  | 2 => 17
  | 3 => 17
  | 4 => 17
  | 5 => 17
  | 6 => 17
  | 7 => 17
  | 8 => 17
  | 9 => 17
  | 10 => 18
  | 11 => 18
  | 12 => 19
  | 13 => 19
  | 14 => 19
  | 15 => 19
  | 16 => 19
  | 17 => 19
  | _ => 19

private theorem resourceRequirements116_116_b37 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 37 (j.val + 1)
      (resources116 (resourceSelector116_37 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116_38 (j : Fin 19) : Fin 20 :=
  match j.val with
  | 0 => 17
  | 1 => 17
  | 2 => 17
  | 3 => 17
  | 4 => 17
  | 5 => 17
  | 6 => 17
  | 7 => 17
  | 8 => 18
  | 9 => 18
  | 10 => 19
  | 11 => 19
  | 12 => 19
  | 13 => 19
  | 14 => 19
  | 15 => 19
  | 16 => 19
  | 17 => 19
  | _ => 19

private theorem resourceRequirements116_116_b38 :
    ∀ j : Fin 19, ResourceRequirements 116 [3, 5, 7, 11] 38 (j.val + 1)
      (resources116 (resourceSelector116_38 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector116 (b : Fin 39) (j : Fin 19) : Fin 20 :=
  match b.val with
  | 0 => resourceSelector116_0 j
  | 1 => resourceSelector116_1 j
  | 2 => resourceSelector116_2 j
  | 3 => resourceSelector116_3 j
  | 4 => resourceSelector116_4 j
  | 5 => resourceSelector116_5 j
  | 6 => resourceSelector116_6 j
  | 7 => resourceSelector116_7 j
  | 8 => resourceSelector116_8 j
  | 9 => resourceSelector116_9 j
  | 10 => resourceSelector116_10 j
  | 11 => resourceSelector116_11 j
  | 12 => resourceSelector116_12 j
  | 13 => resourceSelector116_13 j
  | 14 => resourceSelector116_14 j
  | 15 => resourceSelector116_15 j
  | 16 => resourceSelector116_16 j
  | 17 => resourceSelector116_17 j
  | 18 => resourceSelector116_18 j
  | 19 => resourceSelector116_19 j
  | 20 => resourceSelector116_20 j
  | 21 => resourceSelector116_21 j
  | 22 => resourceSelector116_22 j
  | 23 => resourceSelector116_23 j
  | 24 => resourceSelector116_24 j
  | 25 => resourceSelector116_25 j
  | 26 => resourceSelector116_26 j
  | 27 => resourceSelector116_27 j
  | 28 => resourceSelector116_28 j
  | 29 => resourceSelector116_29 j
  | 30 => resourceSelector116_30 j
  | 31 => resourceSelector116_31 j
  | 32 => resourceSelector116_32 j
  | 33 => resourceSelector116_33 j
  | 34 => resourceSelector116_34 j
  | 35 => resourceSelector116_35 j
  | 36 => resourceSelector116_36 j
  | 37 => resourceSelector116_37 j
  | _ => resourceSelector116_38 j

theorem finiteCheck116_116 : finiteIntervalCheck 116 116 smallOrder116 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 116) (U := 116) (O := smallOrder116) (ps := [3, 5, 7, 11]) resources116 resourceSelector116
  · intro i
    fin_cases i
    · exact validResource116_0
    · exact validResource116_1
    · exact validResource116_2
    · exact validResource116_3
    · exact validResource116_4
    · exact validResource116_5
    · exact validResource116_6
    · exact validResource116_7
    · exact validResource116_8
    · exact validResource116_9
    · exact validResource116_10
    · exact validResource116_11
    · exact validResource116_12
    · exact validResource116_13
    · exact validResource116_14
    · exact validResource116_15
    · exact validResource116_16
    · exact validResource116_17
    · exact validResource116_18
    · exact validResource116_19
  · intro b j
    fin_cases b
    · exact resourceRequirements116_116_b0 j
    · exact resourceRequirements116_116_b1 j
    · exact resourceRequirements116_116_b2 j
    · exact resourceRequirements116_116_b3 j
    · exact resourceRequirements116_116_b4 j
    · exact resourceRequirements116_116_b5 j
    · exact resourceRequirements116_116_b6 j
    · exact resourceRequirements116_116_b7 j
    · exact resourceRequirements116_116_b8 j
    · exact resourceRequirements116_116_b9 j
    · exact resourceRequirements116_116_b10 j
    · exact resourceRequirements116_116_b11 j
    · exact resourceRequirements116_116_b12 j
    · exact resourceRequirements116_116_b13 j
    · exact resourceRequirements116_116_b14 j
    · exact resourceRequirements116_116_b15 j
    · exact resourceRequirements116_116_b16 j
    · exact resourceRequirements116_116_b17 j
    · exact resourceRequirements116_116_b18 j
    · exact resourceRequirements116_116_b19 j
    · exact resourceRequirements116_116_b20 j
    · exact resourceRequirements116_116_b21 j
    · exact resourceRequirements116_116_b22 j
    · exact resourceRequirements116_116_b23 j
    · exact resourceRequirements116_116_b24 j
    · exact resourceRequirements116_116_b25 j
    · exact resourceRequirements116_116_b26 j
    · exact resourceRequirements116_116_b27 j
    · exact resourceRequirements116_116_b28 j
    · exact resourceRequirements116_116_b29 j
    · exact resourceRequirements116_116_b30 j
    · exact resourceRequirements116_116_b31 j
    · exact resourceRequirements116_116_b32 j
    · exact resourceRequirements116_116_b33 j
    · exact resourceRequirements116_116_b34 j
    · exact resourceRequirements116_116_b35 j
    · exact resourceRequirements116_116_b36 j
    · exact resourceRequirements116_116_b37 j
    · exact resourceRequirements116_116_b38 j

theorem exactCertificate116_116 : ExactIntervalCertificate 116 116 smallOrder116 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck116_116
#print axioms smallOrder116_nodup
#print axioms smallOrder116_set
#print axioms finiteCheck116_116
#print axioms exactCertificate116_116
end Erdos883Verified
