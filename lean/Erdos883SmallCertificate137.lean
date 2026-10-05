import Erdos883SmallCertificateSieveCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder137 : List ℕ := [1, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 121, 7, 49, 133, 119, 5, 25, 125, 91, 77, 115, 95, 85, 65, 55, 35, 3, 9, 27, 81, 129, 123, 111, 93, 87, 69, 57, 51, 39, 117, 33, 99, 21, 63, 15, 45, 75, 135, 105]
theorem smallOrder137_nodup : smallOrder137.Nodup := by decide +kernel
theorem smallOrder137_set : smallOrder137.toFinset = oddUniverse 137 := by decide +kernel

private def resources137 (i : Fin 25) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨69, 0, 23, true⟩
  | 1 => ⟨57, 0, 27, true⟩
  | 2 => ⟨53, 0, 30, true⟩
  | 3 => ⟨50, 0, 32, true⟩
  | 4 => ⟨49, 1, 34, true⟩
  | 5 => ⟨46, 0, 38, true⟩
  | 6 => ⟨42, 0, 39, true⟩
  | 7 => ⟨41, 0, 40, true⟩
  | 8 => ⟨40, 0, 41, true⟩
  | 9 => ⟨39, 0, 43, true⟩
  | 10 => ⟨39, 2, 44, true⟩
  | 11 => ⟨38, 2, 45, true⟩
  | 12 => ⟨36, 0, 88, false⟩
  | 13 => ⟨35, 0, 46, true⟩
  | 14 => ⟨34, 0, 47, true⟩
  | 15 => ⟨33, 0, 49, true⟩
  | 16 => ⟨31, 0, 51, true⟩
  | 17 => ⟨29, 0, 52, true⟩
  | 18 => ⟨28, 0, 53, true⟩
  | 19 => ⟨27, 0, 54, true⟩
  | 20 => ⟨26, 0, 56, true⟩
  | 21 => ⟨24, 0, 57, true⟩
  | 22 => ⟨23, 0, 64, true⟩
  | 23 => ⟨16, 0, 65, true⟩
  | _ => ⟨15, 0, 67, true⟩

private def factors137 (v : ℕ) : List ℕ :=
  if v ≤ 67 then
    if v ≤ 33 then
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
              if v ≤ 31 then
                [31]
              else
                [3, 11]
    else
      if v ≤ 49 then
        if v ≤ 41 then
          if v ≤ 37 then
            if v ≤ 35 then
              [5, 7]
            else
              [37]
          else
            if v ≤ 39 then
              [3, 13]
            else
              [41]
        else
          if v ≤ 45 then
            if v ≤ 43 then
              [43]
            else
              [3, 3, 5]
          else
            if v ≤ 47 then
              [47]
            else
              [7, 7]
      else
        if v ≤ 57 then
          if v ≤ 53 then
            if v ≤ 51 then
              [3, 17]
            else
              [53]
          else
            if v ≤ 55 then
              [5, 11]
            else
              [3, 19]
        else
          if v ≤ 61 then
            if v ≤ 59 then
              [59]
            else
              [61]
          else
            if v ≤ 63 then
              [3, 3, 7]
            else
              if v ≤ 65 then
                [5, 13]
              else
                [67]
  else
    if v ≤ 101 then
      if v ≤ 83 then
        if v ≤ 75 then
          if v ≤ 71 then
            if v ≤ 69 then
              [3, 23]
            else
              [71]
          else
            if v ≤ 73 then
              [73]
            else
              [3, 5, 5]
        else
          if v ≤ 79 then
            if v ≤ 77 then
              [7, 11]
            else
              [79]
          else
            if v ≤ 81 then
              [3, 3, 3, 3]
            else
              [83]
      else
        if v ≤ 91 then
          if v ≤ 87 then
            if v ≤ 85 then
              [5, 17]
            else
              [3, 29]
          else
            if v ≤ 89 then
              [89]
            else
              [7, 13]
        else
          if v ≤ 95 then
            if v ≤ 93 then
              [3, 31]
            else
              [5, 19]
          else
            if v ≤ 97 then
              [97]
            else
              if v ≤ 99 then
                [3, 3, 11]
              else
                [101]
    else
      if v ≤ 119 then
        if v ≤ 109 then
          if v ≤ 105 then
            if v ≤ 103 then
              [103]
            else
              [3, 5, 7]
          else
            if v ≤ 107 then
              [107]
            else
              [109]
        else
          if v ≤ 113 then
            if v ≤ 111 then
              [3, 37]
            else
              [113]
          else
            if v ≤ 115 then
              [5, 23]
            else
              if v ≤ 117 then
                [3, 3, 13]
              else
                [7, 17]
      else
        if v ≤ 127 then
          if v ≤ 123 then
            if v ≤ 121 then
              [11, 11]
            else
              [3, 41]
          else
            if v ≤ 125 then
              [5, 5, 5]
            else
              [127]
        else
          if v ≤ 131 then
            if v ≤ 129 then
              [3, 43]
            else
              [131]
          else
            if v ≤ 133 then
              [7, 19]
            else
              if v ≤ 135 then
                [3, 3, 3, 5]
              else
                [137]

private theorem factorsValid137 : FactorDataValid smallOrder137 factors137 := by
  unfold FactorDataValid
  decide +kernel

private theorem validResource137_0 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 0) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_1 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 1) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_2 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 2) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_3 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 3) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_4 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 4) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_5 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 5) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_6 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 6) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_7 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 7) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_8 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 8) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_9 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 9) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_10 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 10) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_11 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 11) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_12 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 12) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_13 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 13) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_14 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 14) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_15 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 15) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_16 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 16) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_17 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 17) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_18 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 18) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_19 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 19) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_20 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 20) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_21 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 21) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_22 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 22) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_23 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 23) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private theorem validResource137_24 :
    PrefixResourceValid 137 smallOrder137 [3, 5, 7, 11] (resources137 24) := by
  apply prefixResourceValid_of_sieveCheck factorsValid137
  decide +kernel

private def resourceSelector137_0 (j : Fin 22) : Fin 25 :=
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
  | 20 => 0
  | _ => 0

private theorem resourceRequirements137_137_b0 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 0 (j.val + 1)
      (resources137 (resourceSelector137_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_1 (j : Fin 22) : Fin 25 :=
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
  | 20 => 0
  | _ => 0

private theorem resourceRequirements137_137_b1 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 1 (j.val + 1)
      (resources137 (resourceSelector137_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_2 (j : Fin 22) : Fin 25 :=
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
  | 20 => 1
  | _ => 1

private theorem resourceRequirements137_137_b2 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 2 (j.val + 1)
      (resources137 (resourceSelector137_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_3 (j : Fin 22) : Fin 25 :=
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
  | 20 => 1
  | _ => 1

private theorem resourceRequirements137_137_b3 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 3 (j.val + 1)
      (resources137 (resourceSelector137_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_4 (j : Fin 22) : Fin 25 :=
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
  | 20 => 1
  | _ => 1

private theorem resourceRequirements137_137_b4 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 4 (j.val + 1)
      (resources137 (resourceSelector137_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_5 (j : Fin 22) : Fin 25 :=
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
  | 20 => 1
  | _ => 1

private theorem resourceRequirements137_137_b5 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 5 (j.val + 1)
      (resources137 (resourceSelector137_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_6 (j : Fin 22) : Fin 25 :=
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
  | 20 => 2
  | _ => 2

private theorem resourceRequirements137_137_b6 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 6 (j.val + 1)
      (resources137 (resourceSelector137_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_7 (j : Fin 22) : Fin 25 :=
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
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | _ => 2

private theorem resourceRequirements137_137_b7 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 7 (j.val + 1)
      (resources137 (resourceSelector137_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_8 (j : Fin 22) : Fin 25 :=
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
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | _ => 2

private theorem resourceRequirements137_137_b8 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 8 (j.val + 1)
      (resources137 (resourceSelector137_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_9 (j : Fin 22) : Fin 25 :=
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
  | 18 => 2
  | 19 => 2
  | 20 => 3
  | _ => 3

private theorem resourceRequirements137_137_b9 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 9 (j.val + 1)
      (resources137 (resourceSelector137_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_10 (j : Fin 22) : Fin 25 :=
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
  | 16 => 2
  | 17 => 2
  | 18 => 3
  | 19 => 3
  | 20 => 3
  | _ => 3

private theorem resourceRequirements137_137_b10 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 10 (j.val + 1)
      (resources137 (resourceSelector137_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_11 (j : Fin 22) : Fin 25 :=
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
  | 14 => 2
  | 15 => 2
  | 16 => 3
  | 17 => 3
  | 18 => 3
  | 19 => 3
  | 20 => 3
  | _ => 4

private theorem resourceRequirements137_137_b11 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 11 (j.val + 1)
      (resources137 (resourceSelector137_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_12 (j : Fin 22) : Fin 25 :=
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
  | 19 => 3
  | 20 => 4
  | _ => 4

private theorem resourceRequirements137_137_b12 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 12 (j.val + 1)
      (resources137 (resourceSelector137_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_13 (j : Fin 22) : Fin 25 :=
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
  | 18 => 3
  | 19 => 4
  | 20 => 5
  | _ => 5

private theorem resourceRequirements137_137_b13 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 13 (j.val + 1)
      (resources137 (resourceSelector137_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_14 (j : Fin 22) : Fin 25 :=
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
  | 17 => 3
  | 18 => 5
  | 19 => 5
  | 20 => 5
  | _ => 5

private theorem resourceRequirements137_137_b14 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 14 (j.val + 1)
      (resources137 (resourceSelector137_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_15 (j : Fin 22) : Fin 25 :=
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
  | 20 => 5
  | _ => 5

private theorem resourceRequirements137_137_b15 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 15 (j.val + 1)
      (resources137 (resourceSelector137_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_16 (j : Fin 22) : Fin 25 :=
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
  | 20 => 5
  | _ => 5

private theorem resourceRequirements137_137_b16 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 16 (j.val + 1)
      (resources137 (resourceSelector137_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_17 (j : Fin 22) : Fin 25 :=
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
  | 18 => 5
  | 19 => 5
  | 20 => 6
  | _ => 6

private theorem resourceRequirements137_137_b17 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 17 (j.val + 1)
      (resources137 (resourceSelector137_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_18 (j : Fin 22) : Fin 25 :=
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
  | 16 => 5
  | 17 => 5
  | 18 => 6
  | 19 => 6
  | 20 => 7
  | _ => 7

private theorem resourceRequirements137_137_b18 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 18 (j.val + 1)
      (resources137 (resourceSelector137_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_19 (j : Fin 22) : Fin 25 :=
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
  | 14 => 5
  | 15 => 5
  | 16 => 6
  | 17 => 6
  | 18 => 7
  | 19 => 7
  | 20 => 8
  | _ => 8

private theorem resourceRequirements137_137_b19 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 19 (j.val + 1)
      (resources137 (resourceSelector137_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_20 (j : Fin 22) : Fin 25 :=
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
  | 12 => 5
  | 13 => 5
  | 14 => 6
  | 15 => 6
  | 16 => 7
  | 17 => 7
  | 18 => 8
  | 19 => 8
  | 20 => 9
  | _ => 9

private theorem resourceRequirements137_137_b20 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 20 (j.val + 1)
      (resources137 (resourceSelector137_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_21 (j : Fin 22) : Fin 25 :=
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
  | 10 => 5
  | 11 => 5
  | 12 => 6
  | 13 => 6
  | 14 => 7
  | 15 => 7
  | 16 => 8
  | 17 => 8
  | 18 => 9
  | 19 => 9
  | 20 => 9
  | _ => 9

private theorem resourceRequirements137_137_b21 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 21 (j.val + 1)
      (resources137 (resourceSelector137_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_22 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 3
  | 1 => 3
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | 7 => 5
  | 8 => 5
  | 9 => 5
  | 10 => 6
  | 11 => 6
  | 12 => 7
  | 13 => 7
  | 14 => 8
  | 15 => 8
  | 16 => 9
  | 17 => 9
  | 18 => 9
  | 19 => 9
  | 20 => 9
  | _ => 10

private theorem resourceRequirements137_137_b22 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 22 (j.val + 1)
      (resources137 (resourceSelector137_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_23 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | 7 => 5
  | 8 => 6
  | 9 => 6
  | 10 => 7
  | 11 => 7
  | 12 => 8
  | 13 => 8
  | 14 => 9
  | 15 => 9
  | 16 => 9
  | 17 => 9
  | 18 => 9
  | 19 => 9
  | 20 => 10
  | _ => 11

private theorem resourceRequirements137_137_b23 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 23 (j.val + 1)
      (resources137 (resourceSelector137_23 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_24 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 6
  | 7 => 6
  | 8 => 7
  | 9 => 7
  | 10 => 8
  | 11 => 8
  | 12 => 9
  | 13 => 9
  | 14 => 9
  | 15 => 9
  | 16 => 9
  | 17 => 9
  | 18 => 9
  | 19 => 12
  | 20 => 13
  | _ => 13

private theorem resourceRequirements137_137_b24 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 24 (j.val + 1)
      (resources137 (resourceSelector137_24 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_25 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 6
  | 5 => 6
  | 6 => 7
  | 7 => 7
  | 8 => 8
  | 9 => 8
  | 10 => 9
  | 11 => 9
  | 12 => 9
  | 13 => 9
  | 14 => 9
  | 15 => 9
  | 16 => 9
  | 17 => 9
  | 18 => 13
  | 19 => 13
  | 20 => 14
  | _ => 14

private theorem resourceRequirements137_137_b25 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 25 (j.val + 1)
      (resources137 (resourceSelector137_25 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_26 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 6
  | 3 => 6
  | 4 => 7
  | 5 => 7
  | 6 => 8
  | 7 => 8
  | 8 => 9
  | 9 => 9
  | 10 => 9
  | 11 => 9
  | 12 => 9
  | 13 => 9
  | 14 => 9
  | 15 => 9
  | 16 => 13
  | 17 => 13
  | 18 => 14
  | 19 => 14
  | 20 => 15
  | _ => 15

private theorem resourceRequirements137_137_b26 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 26 (j.val + 1)
      (resources137 (resourceSelector137_26 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_27 (j : Fin 22) : Fin 25 :=
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
  | 10 => 9
  | 11 => 9
  | 12 => 9
  | 13 => 9
  | 14 => 13
  | 15 => 13
  | 16 => 14
  | 17 => 14
  | 18 => 15
  | 19 => 15
  | 20 => 15
  | _ => 15

private theorem resourceRequirements137_137_b27 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 27 (j.val + 1)
      (resources137 (resourceSelector137_27 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_28 (j : Fin 22) : Fin 25 :=
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
  | 10 => 9
  | 11 => 9
  | 12 => 13
  | 13 => 13
  | 14 => 14
  | 15 => 14
  | 16 => 15
  | 17 => 15
  | 18 => 15
  | 19 => 15
  | 20 => 16
  | _ => 16

private theorem resourceRequirements137_137_b28 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 28 (j.val + 1)
      (resources137 (resourceSelector137_28 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_29 (j : Fin 22) : Fin 25 :=
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
  | 10 => 13
  | 11 => 13
  | 12 => 14
  | 13 => 14
  | 14 => 15
  | 15 => 15
  | 16 => 15
  | 17 => 15
  | 18 => 16
  | 19 => 16
  | 20 => 16
  | _ => 16

private theorem resourceRequirements137_137_b29 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 29 (j.val + 1)
      (resources137 (resourceSelector137_29 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_30 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 9
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | 7 => 9
  | 8 => 13
  | 9 => 13
  | 10 => 14
  | 11 => 14
  | 12 => 15
  | 13 => 15
  | 14 => 15
  | 15 => 15
  | 16 => 16
  | 17 => 16
  | 18 => 16
  | 19 => 16
  | 20 => 17
  | _ => 17

private theorem resourceRequirements137_137_b30 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 30 (j.val + 1)
      (resources137 (resourceSelector137_30 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_31 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 9
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 13
  | 7 => 13
  | 8 => 14
  | 9 => 14
  | 10 => 15
  | 11 => 15
  | 12 => 15
  | 13 => 15
  | 14 => 16
  | 15 => 16
  | 16 => 16
  | 17 => 16
  | 18 => 17
  | 19 => 17
  | 20 => 18
  | _ => 18

private theorem resourceRequirements137_137_b31 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 31 (j.val + 1)
      (resources137 (resourceSelector137_31 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_32 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 9
  | 3 => 9
  | 4 => 13
  | 5 => 13
  | 6 => 14
  | 7 => 14
  | 8 => 15
  | 9 => 15
  | 10 => 15
  | 11 => 15
  | 12 => 16
  | 13 => 16
  | 14 => 16
  | 15 => 16
  | 16 => 17
  | 17 => 17
  | 18 => 18
  | 19 => 18
  | 20 => 19
  | _ => 19

private theorem resourceRequirements137_137_b32 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 32 (j.val + 1)
      (resources137 (resourceSelector137_32 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_33 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 9
  | 1 => 9
  | 2 => 13
  | 3 => 13
  | 4 => 14
  | 5 => 14
  | 6 => 15
  | 7 => 15
  | 8 => 15
  | 9 => 15
  | 10 => 16
  | 11 => 16
  | 12 => 16
  | 13 => 16
  | 14 => 17
  | 15 => 17
  | 16 => 18
  | 17 => 18
  | 18 => 19
  | 19 => 19
  | 20 => 20
  | _ => 20

private theorem resourceRequirements137_137_b33 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 33 (j.val + 1)
      (resources137 (resourceSelector137_33 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_34 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 13
  | 1 => 13
  | 2 => 14
  | 3 => 14
  | 4 => 15
  | 5 => 15
  | 6 => 15
  | 7 => 15
  | 8 => 16
  | 9 => 16
  | 10 => 16
  | 11 => 16
  | 12 => 17
  | 13 => 17
  | 14 => 18
  | 15 => 18
  | 16 => 19
  | 17 => 19
  | 18 => 20
  | 19 => 20
  | 20 => 20
  | _ => 20

private theorem resourceRequirements137_137_b34 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 34 (j.val + 1)
      (resources137 (resourceSelector137_34 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_35 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 14
  | 1 => 14
  | 2 => 15
  | 3 => 15
  | 4 => 15
  | 5 => 15
  | 6 => 16
  | 7 => 16
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
  | 18 => 20
  | 19 => 20
  | 20 => 21
  | _ => 21

private theorem resourceRequirements137_137_b35 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 35 (j.val + 1)
      (resources137 (resourceSelector137_35 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_36 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 15
  | 1 => 15
  | 2 => 15
  | 3 => 15
  | 4 => 16
  | 5 => 16
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
  | 18 => 21
  | 19 => 21
  | 20 => 22
  | _ => 22

private theorem resourceRequirements137_137_b36 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 36 (j.val + 1)
      (resources137 (resourceSelector137_36 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_37 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 15
  | 1 => 15
  | 2 => 16
  | 3 => 16
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
  | 16 => 21
  | 17 => 21
  | 18 => 22
  | 19 => 22
  | 20 => 22
  | _ => 22

private theorem resourceRequirements137_137_b37 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 37 (j.val + 1)
      (resources137 (resourceSelector137_37 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_38 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 16
  | 1 => 16
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
  | 14 => 21
  | 15 => 21
  | 16 => 22
  | 17 => 22
  | 18 => 22
  | 19 => 22
  | 20 => 22
  | _ => 22

private theorem resourceRequirements137_137_b38 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 38 (j.val + 1)
      (resources137 (resourceSelector137_38 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_39 (j : Fin 22) : Fin 25 :=
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
  | 12 => 21
  | 13 => 21
  | 14 => 22
  | 15 => 22
  | 16 => 22
  | 17 => 22
  | 18 => 22
  | 19 => 22
  | 20 => 22
  | _ => 22

private theorem resourceRequirements137_137_b39 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 39 (j.val + 1)
      (resources137 (resourceSelector137_39 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_40 (j : Fin 22) : Fin 25 :=
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
  | 10 => 21
  | 11 => 21
  | 12 => 22
  | 13 => 22
  | 14 => 22
  | 15 => 22
  | 16 => 22
  | 17 => 22
  | 18 => 22
  | 19 => 22
  | 20 => 22
  | _ => 22

private theorem resourceRequirements137_137_b40 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 40 (j.val + 1)
      (resources137 (resourceSelector137_40 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_41 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 18
  | 1 => 18
  | 2 => 19
  | 3 => 19
  | 4 => 20
  | 5 => 20
  | 6 => 20
  | 7 => 20
  | 8 => 21
  | 9 => 21
  | 10 => 22
  | 11 => 22
  | 12 => 22
  | 13 => 22
  | 14 => 22
  | 15 => 22
  | 16 => 22
  | 17 => 22
  | 18 => 22
  | 19 => 22
  | 20 => 22
  | _ => 22

private theorem resourceRequirements137_137_b41 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 41 (j.val + 1)
      (resources137 (resourceSelector137_41 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_42 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 19
  | 1 => 19
  | 2 => 20
  | 3 => 20
  | 4 => 20
  | 5 => 20
  | 6 => 21
  | 7 => 21
  | 8 => 22
  | 9 => 22
  | 10 => 22
  | 11 => 22
  | 12 => 22
  | 13 => 22
  | 14 => 22
  | 15 => 22
  | 16 => 22
  | 17 => 22
  | 18 => 22
  | 19 => 22
  | 20 => 22
  | _ => 22

private theorem resourceRequirements137_137_b42 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 42 (j.val + 1)
      (resources137 (resourceSelector137_42 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_43 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 20
  | 1 => 20
  | 2 => 20
  | 3 => 20
  | 4 => 21
  | 5 => 21
  | 6 => 22
  | 7 => 22
  | 8 => 22
  | 9 => 22
  | 10 => 22
  | 11 => 22
  | 12 => 22
  | 13 => 22
  | 14 => 22
  | 15 => 22
  | 16 => 22
  | 17 => 22
  | 18 => 22
  | 19 => 22
  | 20 => 23
  | _ => 23

private theorem resourceRequirements137_137_b43 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 43 (j.val + 1)
      (resources137 (resourceSelector137_43 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_44 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 20
  | 1 => 20
  | 2 => 21
  | 3 => 21
  | 4 => 22
  | 5 => 22
  | 6 => 22
  | 7 => 22
  | 8 => 22
  | 9 => 22
  | 10 => 22
  | 11 => 22
  | 12 => 22
  | 13 => 22
  | 14 => 22
  | 15 => 22
  | 16 => 22
  | 17 => 22
  | 18 => 23
  | 19 => 23
  | 20 => 24
  | _ => 24

private theorem resourceRequirements137_137_b44 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 44 (j.val + 1)
      (resources137 (resourceSelector137_44 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137_45 (j : Fin 22) : Fin 25 :=
  match j.val with
  | 0 => 21
  | 1 => 21
  | 2 => 22
  | 3 => 22
  | 4 => 22
  | 5 => 22
  | 6 => 22
  | 7 => 22
  | 8 => 22
  | 9 => 22
  | 10 => 22
  | 11 => 22
  | 12 => 22
  | 13 => 22
  | 14 => 22
  | 15 => 22
  | 16 => 23
  | 17 => 23
  | 18 => 24
  | 19 => 24
  | 20 => 24
  | _ => 24

private theorem resourceRequirements137_137_b45 :
    ∀ j : Fin 22, ResourceRequirements 137 [3, 5, 7, 11] 45 (j.val + 1)
      (resources137 (resourceSelector137_45 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector137 (b : Fin 46) (j : Fin 22) : Fin 25 :=
  match b.val with
  | 0 => resourceSelector137_0 j
  | 1 => resourceSelector137_1 j
  | 2 => resourceSelector137_2 j
  | 3 => resourceSelector137_3 j
  | 4 => resourceSelector137_4 j
  | 5 => resourceSelector137_5 j
  | 6 => resourceSelector137_6 j
  | 7 => resourceSelector137_7 j
  | 8 => resourceSelector137_8 j
  | 9 => resourceSelector137_9 j
  | 10 => resourceSelector137_10 j
  | 11 => resourceSelector137_11 j
  | 12 => resourceSelector137_12 j
  | 13 => resourceSelector137_13 j
  | 14 => resourceSelector137_14 j
  | 15 => resourceSelector137_15 j
  | 16 => resourceSelector137_16 j
  | 17 => resourceSelector137_17 j
  | 18 => resourceSelector137_18 j
  | 19 => resourceSelector137_19 j
  | 20 => resourceSelector137_20 j
  | 21 => resourceSelector137_21 j
  | 22 => resourceSelector137_22 j
  | 23 => resourceSelector137_23 j
  | 24 => resourceSelector137_24 j
  | 25 => resourceSelector137_25 j
  | 26 => resourceSelector137_26 j
  | 27 => resourceSelector137_27 j
  | 28 => resourceSelector137_28 j
  | 29 => resourceSelector137_29 j
  | 30 => resourceSelector137_30 j
  | 31 => resourceSelector137_31 j
  | 32 => resourceSelector137_32 j
  | 33 => resourceSelector137_33 j
  | 34 => resourceSelector137_34 j
  | 35 => resourceSelector137_35 j
  | 36 => resourceSelector137_36 j
  | 37 => resourceSelector137_37 j
  | 38 => resourceSelector137_38 j
  | 39 => resourceSelector137_39 j
  | 40 => resourceSelector137_40 j
  | 41 => resourceSelector137_41 j
  | 42 => resourceSelector137_42 j
  | 43 => resourceSelector137_43 j
  | 44 => resourceSelector137_44 j
  | _ => resourceSelector137_45 j

theorem finiteCheck137_137 : finiteIntervalCheck 137 137 smallOrder137 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 137) (U := 137) (O := smallOrder137) (ps := [3, 5, 7, 11]) resources137 resourceSelector137
  · intro i
    fin_cases i
    · exact validResource137_0
    · exact validResource137_1
    · exact validResource137_2
    · exact validResource137_3
    · exact validResource137_4
    · exact validResource137_5
    · exact validResource137_6
    · exact validResource137_7
    · exact validResource137_8
    · exact validResource137_9
    · exact validResource137_10
    · exact validResource137_11
    · exact validResource137_12
    · exact validResource137_13
    · exact validResource137_14
    · exact validResource137_15
    · exact validResource137_16
    · exact validResource137_17
    · exact validResource137_18
    · exact validResource137_19
    · exact validResource137_20
    · exact validResource137_21
    · exact validResource137_22
    · exact validResource137_23
    · exact validResource137_24
  · intro b j
    fin_cases b
    · exact resourceRequirements137_137_b0 j
    · exact resourceRequirements137_137_b1 j
    · exact resourceRequirements137_137_b2 j
    · exact resourceRequirements137_137_b3 j
    · exact resourceRequirements137_137_b4 j
    · exact resourceRequirements137_137_b5 j
    · exact resourceRequirements137_137_b6 j
    · exact resourceRequirements137_137_b7 j
    · exact resourceRequirements137_137_b8 j
    · exact resourceRequirements137_137_b9 j
    · exact resourceRequirements137_137_b10 j
    · exact resourceRequirements137_137_b11 j
    · exact resourceRequirements137_137_b12 j
    · exact resourceRequirements137_137_b13 j
    · exact resourceRequirements137_137_b14 j
    · exact resourceRequirements137_137_b15 j
    · exact resourceRequirements137_137_b16 j
    · exact resourceRequirements137_137_b17 j
    · exact resourceRequirements137_137_b18 j
    · exact resourceRequirements137_137_b19 j
    · exact resourceRequirements137_137_b20 j
    · exact resourceRequirements137_137_b21 j
    · exact resourceRequirements137_137_b22 j
    · exact resourceRequirements137_137_b23 j
    · exact resourceRequirements137_137_b24 j
    · exact resourceRequirements137_137_b25 j
    · exact resourceRequirements137_137_b26 j
    · exact resourceRequirements137_137_b27 j
    · exact resourceRequirements137_137_b28 j
    · exact resourceRequirements137_137_b29 j
    · exact resourceRequirements137_137_b30 j
    · exact resourceRequirements137_137_b31 j
    · exact resourceRequirements137_137_b32 j
    · exact resourceRequirements137_137_b33 j
    · exact resourceRequirements137_137_b34 j
    · exact resourceRequirements137_137_b35 j
    · exact resourceRequirements137_137_b36 j
    · exact resourceRequirements137_137_b37 j
    · exact resourceRequirements137_137_b38 j
    · exact resourceRequirements137_137_b39 j
    · exact resourceRequirements137_137_b40 j
    · exact resourceRequirements137_137_b41 j
    · exact resourceRequirements137_137_b42 j
    · exact resourceRequirements137_137_b43 j
    · exact resourceRequirements137_137_b44 j
    · exact resourceRequirements137_137_b45 j

theorem exactCertificate137_137 : ExactIntervalCertificate 137 137 smallOrder137 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck137_137
#print axioms smallOrder137_nodup
#print axioms smallOrder137_set
#print axioms finiteCheck137_137
#print axioms exactCertificate137_137
end Erdos883Verified
