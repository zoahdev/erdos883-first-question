import Erdos883SmallCertificateSieveCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder130 : List ℕ := [1, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 121, 7, 49, 119, 5, 25, 125, 91, 77, 115, 95, 85, 65, 55, 35, 3, 9, 27, 81, 129, 123, 111, 93, 87, 69, 57, 51, 39, 117, 33, 99, 21, 63, 15, 45, 75, 105]
theorem smallOrder130_nodup : smallOrder130.Nodup := by decide +kernel
theorem smallOrder130_set : smallOrder130.toFinset = oddUniverse 130 := by decide +kernel

private def resources130 (i : Fin 23) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨65, 0, 20, true⟩
  | 1 => ⟨55, 0, 25, true⟩
  | 2 => ⟨50, 0, 28, true⟩
  | 3 => ⟨47, 0, 30, true⟩
  | 4 => ⟨47, 1, 32, true⟩
  | 5 => ⟨43, 0, 35, true⟩
  | 6 => ⟨40, 0, 37, true⟩
  | 7 => ⟨38, 0, 38, true⟩
  | 8 => ⟨37, 0, 40, true⟩
  | 9 => ⟨35, 0, 41, true⟩
  | 10 => ⟨37, 2, 43, true⟩
  | 11 => ⟨34, 0, 84, false⟩
  | 12 => ⟨32, 0, 44, true⟩
  | 13 => ⟨31, 0, 46, true⟩
  | 14 => ⟨29, 0, 48, true⟩
  | 15 => ⟨27, 0, 49, true⟩
  | 16 => ⟨26, 0, 50, true⟩
  | 17 => ⟨25, 0, 51, true⟩
  | 18 => ⟨24, 0, 53, true⟩
  | 19 => ⟨22, 0, 54, true⟩
  | 20 => ⟨21, 0, 60, true⟩
  | 21 => ⟨15, 0, 61, true⟩
  | _ => ⟨14, 0, 63, true⟩

private def factors130 (v : ℕ) : List ℕ :=
  if v ≤ 63 then
    if v ≤ 31 then
      if v ≤ 15 then
        if v ≤ 7 then
          if v ≤ 3 then
            if v ≤ 1 then
              []
            else
              [3]
          else
            if v ≤ 5 then
              [5]
            else
              [7]
        else
          if v ≤ 11 then
            if v ≤ 9 then
              [3, 3]
            else
              [11]
          else
            if v ≤ 13 then
              [13]
            else
              [3, 5]
      else
        if v ≤ 23 then
          if v ≤ 19 then
            if v ≤ 17 then
              [17]
            else
              [19]
          else
            if v ≤ 21 then
              [3, 7]
            else
              [23]
        else
          if v ≤ 27 then
            if v ≤ 25 then
              [5, 5]
            else
              [3, 3, 3]
          else
            if v ≤ 29 then
              [29]
            else
              [31]
    else
      if v ≤ 47 then
        if v ≤ 39 then
          if v ≤ 35 then
            if v ≤ 33 then
              [3, 11]
            else
              [5, 7]
          else
            if v ≤ 37 then
              [37]
            else
              [3, 13]
        else
          if v ≤ 43 then
            if v ≤ 41 then
              [41]
            else
              [43]
          else
            if v ≤ 45 then
              [3, 3, 5]
            else
              [47]
      else
        if v ≤ 55 then
          if v ≤ 51 then
            if v ≤ 49 then
              [7, 7]
            else
              [3, 17]
          else
            if v ≤ 53 then
              [53]
            else
              [5, 11]
        else
          if v ≤ 59 then
            if v ≤ 57 then
              [3, 19]
            else
              [59]
          else
            if v ≤ 61 then
              [61]
            else
              [3, 3, 7]
  else
    if v ≤ 95 then
      if v ≤ 79 then
        if v ≤ 71 then
          if v ≤ 67 then
            if v ≤ 65 then
              [5, 13]
            else
              [67]
          else
            if v ≤ 69 then
              [3, 23]
            else
              [71]
        else
          if v ≤ 75 then
            if v ≤ 73 then
              [73]
            else
              [3, 5, 5]
          else
            if v ≤ 77 then
              [7, 11]
            else
              [79]
      else
        if v ≤ 87 then
          if v ≤ 83 then
            if v ≤ 81 then
              [3, 3, 3, 3]
            else
              [83]
          else
            if v ≤ 85 then
              [5, 17]
            else
              [3, 29]
        else
          if v ≤ 91 then
            if v ≤ 89 then
              [89]
            else
              [7, 13]
          else
            if v ≤ 93 then
              [3, 31]
            else
              [5, 19]
    else
      if v ≤ 111 then
        if v ≤ 103 then
          if v ≤ 99 then
            if v ≤ 97 then
              [97]
            else
              [3, 3, 11]
          else
            if v ≤ 101 then
              [101]
            else
              [103]
        else
          if v ≤ 107 then
            if v ≤ 105 then
              [3, 5, 7]
            else
              [107]
          else
            if v ≤ 109 then
              [109]
            else
              [3, 37]
      else
        if v ≤ 119 then
          if v ≤ 115 then
            if v ≤ 113 then
              [113]
            else
              [5, 23]
          else
            if v ≤ 117 then
              [3, 3, 13]
            else
              [7, 17]
        else
          if v ≤ 123 then
            if v ≤ 121 then
              [11, 11]
            else
              [3, 41]
          else
            if v ≤ 125 then
              [5, 5, 5]
            else
              if v ≤ 127 then
                [127]
              else
                [3, 43]

private theorem factorsValid130 : FactorDataValid smallOrder130 factors130 := by
  unfold FactorDataValid
  decide +kernel

private theorem validResource130_0 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 0) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_1 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 1) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_2 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 2) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_3 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 3) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_4 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 4) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_5 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 5) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_6 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 6) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_7 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 7) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_8 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 8) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_9 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 9) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_10 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 10) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_11 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 11) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_12 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 12) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_13 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 13) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_14 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 14) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_15 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 15) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_16 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 16) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_17 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 17) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_18 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 18) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_19 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 19) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_20 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 20) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_21 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 21) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private theorem validResource130_22 :
    PrefixResourceValid 130 smallOrder130 [3, 5, 7, 11] (resources130 22) := by
  apply prefixResourceValid_of_sieveCheck factorsValid130
  decide +kernel

private def resourceSelector130_0 (j : Fin 21) : Fin 23 :=
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
  | 18 => 0
  | 19 => 0
  | _ => 1

private theorem resourceRequirements130_130_b0 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 0 (j.val + 1)
      (resources130 (resourceSelector130_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_1 (j : Fin 21) : Fin 23 :=
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
  | 18 => 1
  | 19 => 1
  | _ => 1

private theorem resourceRequirements130_130_b1 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 1 (j.val + 1)
      (resources130 (resourceSelector130_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_2 (j : Fin 21) : Fin 23 :=
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
  | 18 => 1
  | 19 => 1
  | _ => 1

private theorem resourceRequirements130_130_b2 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 2 (j.val + 1)
      (resources130 (resourceSelector130_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_3 (j : Fin 21) : Fin 23 :=
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
  | 18 => 1
  | 19 => 1
  | _ => 1

private theorem resourceRequirements130_130_b3 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 3 (j.val + 1)
      (resources130 (resourceSelector130_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_4 (j : Fin 21) : Fin 23 :=
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
  | 18 => 1
  | 19 => 1
  | _ => 1

private theorem resourceRequirements130_130_b4 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 4 (j.val + 1)
      (resources130 (resourceSelector130_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_5 (j : Fin 21) : Fin 23 :=
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
  | 18 => 1
  | 19 => 1
  | _ => 2

private theorem resourceRequirements130_130_b5 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 5 (j.val + 1)
      (resources130 (resourceSelector130_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_6 (j : Fin 21) : Fin 23 :=
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
  | 16 => 1
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | _ => 2

private theorem resourceRequirements130_130_b6 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 6 (j.val + 1)
      (resources130 (resourceSelector130_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_7 (j : Fin 21) : Fin 23 :=
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
  | 14 => 1
  | 15 => 1
  | 16 => 2
  | 17 => 2
  | 18 => 2
  | 19 => 2
  | _ => 2

private theorem resourceRequirements130_130_b7 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 7 (j.val + 1)
      (resources130 (resourceSelector130_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_8 (j : Fin 21) : Fin 23 :=
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
  | 12 => 1
  | 13 => 1
  | 14 => 2
  | 15 => 2
  | 16 => 2
  | 17 => 2
  | 18 => 2
  | 19 => 2
  | _ => 3

private theorem resourceRequirements130_130_b8 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 8 (j.val + 1)
      (resources130 (resourceSelector130_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_9 (j : Fin 21) : Fin 23 :=
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
  | 10 => 1
  | 11 => 1
  | 12 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 2
  | 16 => 2
  | 17 => 2
  | 18 => 3
  | 19 => 3
  | _ => 3

private theorem resourceRequirements130_130_b9 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 9 (j.val + 1)
      (resources130 (resourceSelector130_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_10 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 1
  | 1 => 1
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
  | 14 => 2
  | 15 => 2
  | 16 => 3
  | 17 => 3
  | 18 => 3
  | 19 => 3
  | _ => 4

private theorem resourceRequirements130_130_b10 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 10 (j.val + 1)
      (resources130 (resourceSelector130_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_11 (j : Fin 21) : Fin 23 :=
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
  | 12 => 2
  | 13 => 2
  | 14 => 3
  | 15 => 3
  | 16 => 3
  | 17 => 3
  | 18 => 3
  | 19 => 4
  | _ => 4

private theorem resourceRequirements130_130_b11 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 11 (j.val + 1)
      (resources130 (resourceSelector130_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_12 (j : Fin 21) : Fin 23 :=
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
  | 10 => 2
  | 11 => 2
  | 12 => 3
  | 13 => 3
  | 14 => 3
  | 15 => 3
  | 16 => 3
  | 17 => 3
  | 18 => 4
  | 19 => 4
  | _ => 5

private theorem resourceRequirements130_130_b12 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 12 (j.val + 1)
      (resources130 (resourceSelector130_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_13 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
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
  | 16 => 3
  | 17 => 4
  | 18 => 5
  | 19 => 5
  | _ => 5

private theorem resourceRequirements130_130_b13 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 13 (j.val + 1)
      (resources130 (resourceSelector130_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_14 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
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
  | 15 => 3
  | 16 => 5
  | 17 => 5
  | 18 => 5
  | 19 => 5
  | _ => 5

private theorem resourceRequirements130_130_b14 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 14 (j.val + 1)
      (resources130 (resourceSelector130_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_15 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 2
  | 1 => 2
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
  | 18 => 5
  | 19 => 5
  | _ => 6

private theorem resourceRequirements130_130_b15 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 15 (j.val + 1)
      (resources130 (resourceSelector130_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_16 (j : Fin 21) : Fin 23 :=
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
  | 18 => 6
  | 19 => 6
  | _ => 6

private theorem resourceRequirements130_130_b16 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 16 (j.val + 1)
      (resources130 (resourceSelector130_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_17 (j : Fin 21) : Fin 23 :=
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
  | 18 => 6
  | 19 => 6
  | _ => 7

private theorem resourceRequirements130_130_b17 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 17 (j.val + 1)
      (resources130 (resourceSelector130_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_18 (j : Fin 21) : Fin 23 :=
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
  | 18 => 7
  | 19 => 7
  | _ => 8

private theorem resourceRequirements130_130_b18 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 18 (j.val + 1)
      (resources130 (resourceSelector130_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_19 (j : Fin 21) : Fin 23 :=
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
  | 18 => 8
  | 19 => 8
  | _ => 8

private theorem resourceRequirements130_130_b19 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 19 (j.val + 1)
      (resources130 (resourceSelector130_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_20 (j : Fin 21) : Fin 23 :=
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
  | 18 => 8
  | 19 => 8
  | _ => 9

private theorem resourceRequirements130_130_b20 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 20 (j.val + 1)
      (resources130 (resourceSelector130_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_21 (j : Fin 21) : Fin 23 :=
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
  | 18 => 9
  | 19 => 9
  | _ => 10

private theorem resourceRequirements130_130_b21 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 21 (j.val + 1)
      (resources130 (resourceSelector130_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_22 (j : Fin 21) : Fin 23 :=
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
  | 18 => 9
  | 19 => 11
  | _ => 10

private theorem resourceRequirements130_130_b22 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 22 (j.val + 1)
      (resources130 (resourceSelector130_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_23 (j : Fin 21) : Fin 23 :=
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
  | 18 => 11
  | 19 => 11
  | _ => 12

private theorem resourceRequirements130_130_b23 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 23 (j.val + 1)
      (resources130 (resourceSelector130_23 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_24 (j : Fin 21) : Fin 23 :=
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
  | 16 => 9
  | 17 => 11
  | 18 => 12
  | 19 => 12
  | _ => 13

private theorem resourceRequirements130_130_b24 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 24 (j.val + 1)
      (resources130 (resourceSelector130_24 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_25 (j : Fin 21) : Fin 23 :=
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
  | 14 => 9
  | 15 => 9
  | 16 => 12
  | 17 => 12
  | 18 => 13
  | 19 => 13
  | _ => 13

private theorem resourceRequirements130_130_b25 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 25 (j.val + 1)
      (resources130 (resourceSelector130_25 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_26 (j : Fin 21) : Fin 23 :=
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
  | 12 => 9
  | 13 => 9
  | 14 => 12
  | 15 => 12
  | 16 => 13
  | 17 => 13
  | 18 => 13
  | 19 => 13
  | _ => 14

private theorem resourceRequirements130_130_b26 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 26 (j.val + 1)
      (resources130 (resourceSelector130_26 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_27 (j : Fin 21) : Fin 23 :=
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
  | 10 => 9
  | 11 => 9
  | 12 => 12
  | 13 => 12
  | 14 => 13
  | 15 => 13
  | 16 => 13
  | 17 => 13
  | 18 => 14
  | 19 => 14
  | _ => 14

private theorem resourceRequirements130_130_b27 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 27 (j.val + 1)
      (resources130 (resourceSelector130_27 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_28 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 8
  | 3 => 8
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | 7 => 9
  | 8 => 9
  | 9 => 9
  | 10 => 12
  | 11 => 12
  | 12 => 13
  | 13 => 13
  | 14 => 13
  | 15 => 13
  | 16 => 14
  | 17 => 14
  | 18 => 14
  | 19 => 14
  | _ => 15

private theorem resourceRequirements130_130_b28 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 28 (j.val + 1)
      (resources130 (resourceSelector130_28 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_29 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 9
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | 7 => 9
  | 8 => 12
  | 9 => 12
  | 10 => 13
  | 11 => 13
  | 12 => 13
  | 13 => 13
  | 14 => 14
  | 15 => 14
  | 16 => 14
  | 17 => 14
  | 18 => 15
  | 19 => 15
  | _ => 16

private theorem resourceRequirements130_130_b29 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 29 (j.val + 1)
      (resources130 (resourceSelector130_29 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_30 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 9
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 12
  | 7 => 12
  | 8 => 13
  | 9 => 13
  | 10 => 13
  | 11 => 13
  | 12 => 14
  | 13 => 14
  | 14 => 14
  | 15 => 14
  | 16 => 15
  | 17 => 15
  | 18 => 16
  | 19 => 16
  | _ => 17

private theorem resourceRequirements130_130_b30 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 30 (j.val + 1)
      (resources130 (resourceSelector130_30 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_31 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 9
  | 3 => 9
  | 4 => 12
  | 5 => 12
  | 6 => 13
  | 7 => 13
  | 8 => 13
  | 9 => 13
  | 10 => 14
  | 11 => 14
  | 12 => 14
  | 13 => 14
  | 14 => 15
  | 15 => 15
  | 16 => 16
  | 17 => 16
  | 18 => 17
  | 19 => 17
  | _ => 18

private theorem resourceRequirements130_130_b31 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 31 (j.val + 1)
      (resources130 (resourceSelector130_31 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_32 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 12
  | 3 => 12
  | 4 => 13
  | 5 => 13
  | 6 => 13
  | 7 => 13
  | 8 => 14
  | 9 => 14
  | 10 => 14
  | 11 => 14
  | 12 => 15
  | 13 => 15
  | 14 => 16
  | 15 => 16
  | 16 => 17
  | 17 => 17
  | 18 => 18
  | 19 => 18
  | _ => 18

private theorem resourceRequirements130_130_b32 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 32 (j.val + 1)
      (resources130 (resourceSelector130_32 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_33 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 12
  | 1 => 12
  | 2 => 13
  | 3 => 13
  | 4 => 13
  | 5 => 13
  | 6 => 14
  | 7 => 14
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
  | 18 => 18
  | 19 => 18
  | _ => 19

private theorem resourceRequirements130_130_b33 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 33 (j.val + 1)
      (resources130 (resourceSelector130_33 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_34 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 13
  | 1 => 13
  | 2 => 13
  | 3 => 13
  | 4 => 14
  | 5 => 14
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
  | 16 => 18
  | 17 => 18
  | 18 => 19
  | 19 => 19
  | _ => 20

private theorem resourceRequirements130_130_b34 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 34 (j.val + 1)
      (resources130 (resourceSelector130_34 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_35 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 13
  | 1 => 13
  | 2 => 14
  | 3 => 14
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
  | 14 => 18
  | 15 => 18
  | 16 => 19
  | 17 => 19
  | 18 => 20
  | 19 => 20
  | _ => 20

private theorem resourceRequirements130_130_b35 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 35 (j.val + 1)
      (resources130 (resourceSelector130_35 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_36 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 14
  | 1 => 14
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
  | 12 => 18
  | 13 => 18
  | 14 => 19
  | 15 => 19
  | 16 => 20
  | 17 => 20
  | 18 => 20
  | 19 => 20
  | _ => 20

private theorem resourceRequirements130_130_b36 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 36 (j.val + 1)
      (resources130 (resourceSelector130_36 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_37 (j : Fin 21) : Fin 23 :=
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
  | 10 => 18
  | 11 => 18
  | 12 => 19
  | 13 => 19
  | 14 => 20
  | 15 => 20
  | 16 => 20
  | 17 => 20
  | 18 => 20
  | 19 => 20
  | _ => 20

private theorem resourceRequirements130_130_b37 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 37 (j.val + 1)
      (resources130 (resourceSelector130_37 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_38 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 15
  | 1 => 15
  | 2 => 16
  | 3 => 16
  | 4 => 17
  | 5 => 17
  | 6 => 18
  | 7 => 18
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
  | 18 => 20
  | 19 => 20
  | _ => 20

private theorem resourceRequirements130_130_b38 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 38 (j.val + 1)
      (resources130 (resourceSelector130_38 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_39 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 16
  | 1 => 16
  | 2 => 17
  | 3 => 17
  | 4 => 18
  | 5 => 18
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
  | 18 => 20
  | 19 => 20
  | _ => 20

private theorem resourceRequirements130_130_b39 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 39 (j.val + 1)
      (resources130 (resourceSelector130_39 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_40 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 17
  | 1 => 17
  | 2 => 18
  | 3 => 18
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
  | 18 => 20
  | 19 => 20
  | _ => 21

private theorem resourceRequirements130_130_b40 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 40 (j.val + 1)
      (resources130 (resourceSelector130_40 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_41 (j : Fin 21) : Fin 23 :=
  match j.val with
  | 0 => 18
  | 1 => 18
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
  | 16 => 20
  | 17 => 20
  | 18 => 21
  | 19 => 21
  | _ => 22

private theorem resourceRequirements130_130_b41 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 41 (j.val + 1)
      (resources130 (resourceSelector130_41 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130_42 (j : Fin 21) : Fin 23 :=
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
  | 14 => 20
  | 15 => 20
  | 16 => 21
  | 17 => 21
  | 18 => 22
  | 19 => 22
  | _ => 22

private theorem resourceRequirements130_130_b42 :
    ∀ j : Fin 21, ResourceRequirements 130 [3, 5, 7, 11] 42 (j.val + 1)
      (resources130 (resourceSelector130_42 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector130 (b : Fin 43) (j : Fin 21) : Fin 23 :=
  match b.val with
  | 0 => resourceSelector130_0 j
  | 1 => resourceSelector130_1 j
  | 2 => resourceSelector130_2 j
  | 3 => resourceSelector130_3 j
  | 4 => resourceSelector130_4 j
  | 5 => resourceSelector130_5 j
  | 6 => resourceSelector130_6 j
  | 7 => resourceSelector130_7 j
  | 8 => resourceSelector130_8 j
  | 9 => resourceSelector130_9 j
  | 10 => resourceSelector130_10 j
  | 11 => resourceSelector130_11 j
  | 12 => resourceSelector130_12 j
  | 13 => resourceSelector130_13 j
  | 14 => resourceSelector130_14 j
  | 15 => resourceSelector130_15 j
  | 16 => resourceSelector130_16 j
  | 17 => resourceSelector130_17 j
  | 18 => resourceSelector130_18 j
  | 19 => resourceSelector130_19 j
  | 20 => resourceSelector130_20 j
  | 21 => resourceSelector130_21 j
  | 22 => resourceSelector130_22 j
  | 23 => resourceSelector130_23 j
  | 24 => resourceSelector130_24 j
  | 25 => resourceSelector130_25 j
  | 26 => resourceSelector130_26 j
  | 27 => resourceSelector130_27 j
  | 28 => resourceSelector130_28 j
  | 29 => resourceSelector130_29 j
  | 30 => resourceSelector130_30 j
  | 31 => resourceSelector130_31 j
  | 32 => resourceSelector130_32 j
  | 33 => resourceSelector130_33 j
  | 34 => resourceSelector130_34 j
  | 35 => resourceSelector130_35 j
  | 36 => resourceSelector130_36 j
  | 37 => resourceSelector130_37 j
  | 38 => resourceSelector130_38 j
  | 39 => resourceSelector130_39 j
  | 40 => resourceSelector130_40 j
  | 41 => resourceSelector130_41 j
  | _ => resourceSelector130_42 j

theorem finiteCheck130_130 : finiteIntervalCheck 130 130 smallOrder130 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 130) (U := 130) (O := smallOrder130) (ps := [3, 5, 7, 11]) resources130 resourceSelector130
  · intro i
    fin_cases i
    · exact validResource130_0
    · exact validResource130_1
    · exact validResource130_2
    · exact validResource130_3
    · exact validResource130_4
    · exact validResource130_5
    · exact validResource130_6
    · exact validResource130_7
    · exact validResource130_8
    · exact validResource130_9
    · exact validResource130_10
    · exact validResource130_11
    · exact validResource130_12
    · exact validResource130_13
    · exact validResource130_14
    · exact validResource130_15
    · exact validResource130_16
    · exact validResource130_17
    · exact validResource130_18
    · exact validResource130_19
    · exact validResource130_20
    · exact validResource130_21
    · exact validResource130_22
  · intro b j
    fin_cases b
    · exact resourceRequirements130_130_b0 j
    · exact resourceRequirements130_130_b1 j
    · exact resourceRequirements130_130_b2 j
    · exact resourceRequirements130_130_b3 j
    · exact resourceRequirements130_130_b4 j
    · exact resourceRequirements130_130_b5 j
    · exact resourceRequirements130_130_b6 j
    · exact resourceRequirements130_130_b7 j
    · exact resourceRequirements130_130_b8 j
    · exact resourceRequirements130_130_b9 j
    · exact resourceRequirements130_130_b10 j
    · exact resourceRequirements130_130_b11 j
    · exact resourceRequirements130_130_b12 j
    · exact resourceRequirements130_130_b13 j
    · exact resourceRequirements130_130_b14 j
    · exact resourceRequirements130_130_b15 j
    · exact resourceRequirements130_130_b16 j
    · exact resourceRequirements130_130_b17 j
    · exact resourceRequirements130_130_b18 j
    · exact resourceRequirements130_130_b19 j
    · exact resourceRequirements130_130_b20 j
    · exact resourceRequirements130_130_b21 j
    · exact resourceRequirements130_130_b22 j
    · exact resourceRequirements130_130_b23 j
    · exact resourceRequirements130_130_b24 j
    · exact resourceRequirements130_130_b25 j
    · exact resourceRequirements130_130_b26 j
    · exact resourceRequirements130_130_b27 j
    · exact resourceRequirements130_130_b28 j
    · exact resourceRequirements130_130_b29 j
    · exact resourceRequirements130_130_b30 j
    · exact resourceRequirements130_130_b31 j
    · exact resourceRequirements130_130_b32 j
    · exact resourceRequirements130_130_b33 j
    · exact resourceRequirements130_130_b34 j
    · exact resourceRequirements130_130_b35 j
    · exact resourceRequirements130_130_b36 j
    · exact resourceRequirements130_130_b37 j
    · exact resourceRequirements130_130_b38 j
    · exact resourceRequirements130_130_b39 j
    · exact resourceRequirements130_130_b40 j
    · exact resourceRequirements130_130_b41 j
    · exact resourceRequirements130_130_b42 j

theorem exactCertificate130_130 : ExactIntervalCertificate 130 130 smallOrder130 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck130_130
#print axioms smallOrder130_nodup
#print axioms smallOrder130_set
#print axioms finiteCheck130_130
#print axioms exactCertificate130_130
end Erdos883Verified
