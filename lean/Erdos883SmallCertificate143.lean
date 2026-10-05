import Erdos883SmallCertificateSieveCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder143 : List ℕ := [1, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 121, 7, 49, 143, 133, 119, 5, 25, 125, 91, 77, 115, 95, 85, 65, 55, 35, 3, 9, 27, 81, 141, 129, 123, 111, 93, 87, 69, 57, 51, 39, 117, 33, 99, 21, 63, 15, 45, 75, 135, 105]
theorem smallOrder143_nodup : smallOrder143.Nodup := by decide +kernel
theorem smallOrder143_set : smallOrder143.toFinset = oddUniverse 143 := by decide +kernel

private def resources143 (i : Fin 28) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨72, 0, 2, true⟩
  | 1 => ⟨71, 0, 23, true⟩
  | 2 => ⟨60, 0, 27, true⟩
  | 3 => ⟨56, 0, 31, true⟩
  | 4 => ⟨52, 0, 33, true⟩
  | 5 => ⟨52, 1, 35, true⟩
  | 6 => ⟨48, 0, 39, true⟩
  | 7 => ⟨44, 0, 41, true⟩
  | 8 => ⟨42, 0, 42, true⟩
  | 9 => ⟨41, 0, 45, true⟩
  | 10 => ⟨41, 2, 46, true⟩
  | 11 => ⟨38, 0, 93, false⟩
  | 12 => ⟨37, 0, 94, false⟩
  | 13 => ⟨37, 0, 46, true⟩
  | 14 => ⟨36, 0, 94, false⟩
  | 15 => ⟨36, 0, 47, true⟩
  | 16 => ⟨35, 0, 49, true⟩
  | 17 => ⟨34, 0, 51, true⟩
  | 18 => ⟨32, 0, 53, true⟩
  | 19 => ⟨30, 0, 54, true⟩
  | 20 => ⟨29, 0, 55, true⟩
  | 21 => ⟨28, 0, 56, true⟩
  | 22 => ⟨27, 0, 57, true⟩
  | 23 => ⟨26, 0, 58, true⟩
  | 24 => ⟨25, 0, 59, true⟩
  | 25 => ⟨24, 0, 67, true⟩
  | 26 => ⟨16, 0, 68, true⟩
  | _ => ⟨15, 0, 70, true⟩

private def factors143 (v : ℕ) : List ℕ :=
  if v ≤ 71 then
    if v ≤ 35 then
      if v ≤ 17 then
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
              if v ≤ 15 then
                [3, 5]
              else
                [17]
      else
        if v ≤ 25 then
          if v ≤ 21 then
            if v ≤ 19 then
              [19]
            else
              [3, 7]
          else
            if v ≤ 23 then
              [23]
            else
              [5, 5]
        else
          if v ≤ 29 then
            if v ≤ 27 then
              [3, 3, 3]
            else
              [29]
          else
            if v ≤ 31 then
              [31]
            else
              if v ≤ 33 then
                [3, 11]
              else
                [5, 7]
    else
      if v ≤ 53 then
        if v ≤ 43 then
          if v ≤ 39 then
            if v ≤ 37 then
              [37]
            else
              [3, 13]
          else
            if v ≤ 41 then
              [41]
            else
              [43]
        else
          if v ≤ 47 then
            if v ≤ 45 then
              [3, 3, 5]
            else
              [47]
          else
            if v ≤ 49 then
              [7, 7]
            else
              if v ≤ 51 then
                [3, 17]
              else
                [53]
      else
        if v ≤ 61 then
          if v ≤ 57 then
            if v ≤ 55 then
              [5, 11]
            else
              [3, 19]
          else
            if v ≤ 59 then
              [59]
            else
              [61]
        else
          if v ≤ 65 then
            if v ≤ 63 then
              [3, 3, 7]
            else
              [5, 13]
          else
            if v ≤ 67 then
              [67]
            else
              if v ≤ 69 then
                [3, 23]
              else
                [71]
  else
    if v ≤ 107 then
      if v ≤ 89 then
        if v ≤ 79 then
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
          if v ≤ 83 then
            if v ≤ 81 then
              [3, 3, 3, 3]
            else
              [83]
          else
            if v ≤ 85 then
              [5, 17]
            else
              if v ≤ 87 then
                [3, 29]
              else
                [89]
      else
        if v ≤ 97 then
          if v ≤ 93 then
            if v ≤ 91 then
              [7, 13]
            else
              [3, 31]
          else
            if v ≤ 95 then
              [5, 19]
            else
              [97]
        else
          if v ≤ 101 then
            if v ≤ 99 then
              [3, 3, 11]
            else
              [101]
          else
            if v ≤ 103 then
              [103]
            else
              if v ≤ 105 then
                [3, 5, 7]
              else
                [107]
    else
      if v ≤ 125 then
        if v ≤ 115 then
          if v ≤ 111 then
            if v ≤ 109 then
              [109]
            else
              [3, 37]
          else
            if v ≤ 113 then
              [113]
            else
              [5, 23]
        else
          if v ≤ 119 then
            if v ≤ 117 then
              [3, 3, 13]
            else
              [7, 17]
          else
            if v ≤ 121 then
              [11, 11]
            else
              if v ≤ 123 then
                [3, 41]
              else
                [5, 5, 5]
      else
        if v ≤ 133 then
          if v ≤ 129 then
            if v ≤ 127 then
              [127]
            else
              [3, 43]
          else
            if v ≤ 131 then
              [131]
            else
              [7, 19]
        else
          if v ≤ 137 then
            if v ≤ 135 then
              [3, 3, 3, 5]
            else
              [137]
          else
            if v ≤ 139 then
              [139]
            else
              if v ≤ 141 then
                [3, 47]
              else
                [11, 13]

private theorem factorsValid143 : FactorDataValid smallOrder143 factors143 := by
  unfold FactorDataValid
  decide +kernel

private theorem validResource143_0 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 0) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_1 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 1) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_2 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 2) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_3 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 3) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_4 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 4) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_5 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 5) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_6 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 6) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_7 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 7) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_8 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 8) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_9 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 9) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_10 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 10) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_11 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 11) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_12 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 12) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_13 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 13) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_14 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 14) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_15 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 15) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_16 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 16) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_17 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 17) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_18 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 18) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_19 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 19) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_20 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 20) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_21 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 21) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_22 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 22) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_23 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 23) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_24 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 24) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_25 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 25) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_26 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 26) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private theorem validResource143_27 :
    PrefixResourceValid 143 smallOrder143 [3, 5, 7, 11] (resources143 27) := by
  apply prefixResourceValid_of_sieveCheck factorsValid143
  decide +kernel

private def resourceSelector143_0 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 1 then
    0
  else
    1

private theorem resourceRequirements143_143_b0 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 0 (j.val + 1)
      (resources143 (resourceSelector143_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_1 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 21 then
    1
  else
    2

private theorem resourceRequirements143_143_b1 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 1 (j.val + 1)
      (resources143 (resourceSelector143_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_2 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 19 then
    1
  else
    2

private theorem resourceRequirements143_143_b2 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 2 (j.val + 1)
      (resources143 (resourceSelector143_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_3 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 17 then
    1
  else
    2

private theorem resourceRequirements143_143_b3 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 3 (j.val + 1)
      (resources143 (resourceSelector143_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_4 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 15 then
    1
  else
    2

private theorem resourceRequirements143_143_b4 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 4 (j.val + 1)
      (resources143 (resourceSelector143_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_5 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    1
  else
    if j.val ≤ 21 then
      2
    else
      3

private theorem resourceRequirements143_143_b5 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 5 (j.val + 1)
      (resources143 (resourceSelector143_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_6 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    1
  else
    if j.val ≤ 19 then
      2
    else
      3

private theorem resourceRequirements143_143_b6 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 6 (j.val + 1)
      (resources143 (resourceSelector143_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_7 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 9 then
    1
  else
    if j.val ≤ 17 then
      2
    else
      3

private theorem resourceRequirements143_143_b7 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 7 (j.val + 1)
      (resources143 (resourceSelector143_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_8 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 7 then
    1
  else
    if j.val ≤ 15 then
      2
    else
      3

private theorem resourceRequirements143_143_b8 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 8 (j.val + 1)
      (resources143 (resourceSelector143_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_9 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      1
    else
      2
  else
    if j.val ≤ 21 then
      3
    else
      4

private theorem resourceRequirements143_143_b9 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 9 (j.val + 1)
      (resources143 (resourceSelector143_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_10 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      1
    else
      2
  else
    if j.val ≤ 19 then
      3
    else
      4

private theorem resourceRequirements143_143_b10 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 10 (j.val + 1)
      (resources143 (resourceSelector143_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_11 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      1
    else
      2
  else
    if j.val ≤ 17 then
      3
    else
      if j.val ≤ 21 then
        4
      else
        5

private theorem resourceRequirements143_143_b11 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 11 (j.val + 1)
      (resources143 (resourceSelector143_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_12 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      2
    else
      3
  else
    if j.val ≤ 20 then
      4
    else
      5

private theorem resourceRequirements143_143_b12 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 12 (j.val + 1)
      (resources143 (resourceSelector143_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_13 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      2
    else
      3
  else
    if j.val ≤ 19 then
      4
    else
      if j.val ≤ 21 then
        5
      else
        6

private theorem resourceRequirements143_143_b13 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 13 (j.val + 1)
      (resources143 (resourceSelector143_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_14 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      2
    else
      3
  else
    if j.val ≤ 18 then
      4
    else
      if j.val ≤ 19 then
        5
      else
        6

private theorem resourceRequirements143_143_b14 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 14 (j.val + 1)
      (resources143 (resourceSelector143_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_15 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      2
    else
      3
  else
    if j.val ≤ 17 then
      4
    else
      6

private theorem resourceRequirements143_143_b15 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 15 (j.val + 1)
      (resources143 (resourceSelector143_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_16 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 7 then
    3
  else
    if j.val ≤ 15 then
      4
    else
      6

private theorem resourceRequirements143_143_b16 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 16 (j.val + 1)
      (resources143 (resourceSelector143_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_17 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      3
    else
      4
  else
    if j.val ≤ 21 then
      6
    else
      7

private theorem resourceRequirements143_143_b17 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 17 (j.val + 1)
      (resources143 (resourceSelector143_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_18 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      3
    else
      4
  else
    if j.val ≤ 19 then
      6
    else
      7

private theorem resourceRequirements143_143_b18 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 18 (j.val + 1)
      (resources143 (resourceSelector143_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_19 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      3
    else
      4
  else
    if j.val ≤ 17 then
      6
    else
      if j.val ≤ 21 then
        7
      else
        8

private theorem resourceRequirements143_143_b19 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 19 (j.val + 1)
      (resources143 (resourceSelector143_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_20 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      4
    else
      6
  else
    if j.val ≤ 19 then
      7
    else
      if j.val ≤ 21 then
        8
      else
        9

private theorem resourceRequirements143_143_b20 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 20 (j.val + 1)
      (resources143 (resourceSelector143_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_21 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      4
    else
      6
  else
    if j.val ≤ 17 then
      7
    else
      if j.val ≤ 19 then
        8
      else
        9

private theorem resourceRequirements143_143_b21 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 21 (j.val + 1)
      (resources143 (resourceSelector143_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_22 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      4
    else
      6
  else
    if j.val ≤ 15 then
      7
    else
      if j.val ≤ 17 then
        8
      else
        9

private theorem resourceRequirements143_143_b22 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 22 (j.val + 1)
      (resources143 (resourceSelector143_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_23 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 1 then
      4
    else
      if j.val ≤ 9 then
        6
      else
        7
  else
    if j.val ≤ 15 then
      8
    else
      if j.val ≤ 21 then
        9
      else
        10

private theorem resourceRequirements143_143_b23 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 23 (j.val + 1)
      (resources143 (resourceSelector143_23 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_24 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      6
    else
      if j.val ≤ 11 then
        7
      else
        8
  else
    if j.val ≤ 20 then
      9
    else
      if j.val ≤ 21 then
        11
      else
        12

private theorem resourceRequirements143_143_b24 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 24 (j.val + 1)
      (resources143 (resourceSelector143_24 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_25 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      6
    else
      if j.val ≤ 9 then
        7
      else
        8
  else
    if j.val ≤ 20 then
      if j.val ≤ 19 then
        9
      else
        13
    else
      if j.val ≤ 21 then
        12
      else
        14

private theorem resourceRequirements143_143_b25 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 25 (j.val + 1)
      (resources143 (resourceSelector143_25 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_26 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 17 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        6
      else
        7
    else
      if j.val ≤ 9 then
        8
      else
        9
  else
    if j.val ≤ 20 then
      if j.val ≤ 19 then
        13
      else
        15
    else
      if j.val ≤ 21 then
        14
      else
        16

private theorem resourceRequirements143_143_b26 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 26 (j.val + 1)
      (resources143 (resourceSelector143_26 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_27 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 15 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        6
      else
        7
    else
      if j.val ≤ 7 then
        8
      else
        9
  else
    if j.val ≤ 19 then
      if j.val ≤ 17 then
        13
      else
        15
    else
      if j.val ≤ 21 then
        16
      else
        17

private theorem resourceRequirements143_143_b27 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 27 (j.val + 1)
      (resources143 (resourceSelector143_27 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_28 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      7
    else
      if j.val ≤ 5 then
        8
      else
        9
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        13
      else
        15
    else
      if j.val ≤ 19 then
        16
      else
        17

private theorem resourceRequirements143_143_b28 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 28 (j.val + 1)
      (resources143 (resourceSelector143_28 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_29 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        7
      else
        8
    else
      if j.val ≤ 11 then
        9
      else
        13
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        15
      else
        16
    else
      if j.val ≤ 21 then
        17
      else
        18

private theorem resourceRequirements143_143_b29 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 29 (j.val + 1)
      (resources143 (resourceSelector143_29 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_30 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    if j.val ≤ 1 then
      8
    else
      if j.val ≤ 9 then
        9
      else
        13
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        15
      else
        16
    else
      if j.val ≤ 19 then
        17
      else
        18

private theorem resourceRequirements143_143_b30 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 30 (j.val + 1)
      (resources143 (resourceSelector143_30 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_31 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      9
    else
      if j.val ≤ 9 then
        13
      else
        15
  else
    if j.val ≤ 17 then
      if j.val ≤ 13 then
        16
      else
        17
    else
      if j.val ≤ 21 then
        18
      else
        19

private theorem resourceRequirements143_143_b31 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 31 (j.val + 1)
      (resources143 (resourceSelector143_31 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_32 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      if j.val ≤ 5 then
        9
      else
        13
    else
      if j.val ≤ 9 then
        15
      else
        16
  else
    if j.val ≤ 19 then
      if j.val ≤ 15 then
        17
      else
        18
    else
      if j.val ≤ 21 then
        19
      else
        20

private theorem resourceRequirements143_143_b32 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 32 (j.val + 1)
      (resources143 (resourceSelector143_32 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_33 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        9
      else
        13
    else
      if j.val ≤ 7 then
        15
      else
        16
  else
    if j.val ≤ 17 then
      if j.val ≤ 13 then
        17
      else
        18
    else
      if j.val ≤ 19 then
        19
      else
        if j.val ≤ 21 then
          20
        else
          21

private theorem resourceRequirements143_143_b33 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 33 (j.val + 1)
      (resources143 (resourceSelector143_33 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_34 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        9
      else
        13
    else
      if j.val ≤ 5 then
        15
      else
        if j.val ≤ 7 then
          16
        else
          17
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        18
      else
        19
    else
      if j.val ≤ 19 then
        20
      else
        if j.val ≤ 21 then
          21
        else
          22

private theorem resourceRequirements143_143_b34 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 34 (j.val + 1)
      (resources143 (resourceSelector143_34 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_35 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        13
      else
        15
    else
      if j.val ≤ 5 then
        16
      else
        if j.val ≤ 9 then
          17
        else
          18
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        19
      else
        20
    else
      if j.val ≤ 19 then
        21
      else
        if j.val ≤ 21 then
          22
        else
          23

private theorem resourceRequirements143_143_b35 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 35 (j.val + 1)
      (resources143 (resourceSelector143_35 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_36 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        15
      else
        16
    else
      if j.val ≤ 7 then
        17
      else
        if j.val ≤ 11 then
          18
        else
          19
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        20
      else
        21
    else
      if j.val ≤ 19 then
        22
      else
        if j.val ≤ 21 then
          23
        else
          24

private theorem resourceRequirements143_143_b36 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 36 (j.val + 1)
      (resources143 (resourceSelector143_36 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_37 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        16
      else
        17
    else
      if j.val ≤ 9 then
        18
      else
        if j.val ≤ 11 then
          19
        else
          20
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        21
      else
        22
    else
      if j.val ≤ 19 then
        23
      else
        if j.val ≤ 21 then
          24
        else
          25

private theorem resourceRequirements143_143_b37 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 37 (j.val + 1)
      (resources143 (resourceSelector143_37 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_38 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        17
      else
        18
    else
      if j.val ≤ 9 then
        19
      else
        20
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        21
      else
        22
    else
      if j.val ≤ 17 then
        23
      else
        if j.val ≤ 19 then
          24
        else
          25

private theorem resourceRequirements143_143_b38 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 38 (j.val + 1)
      (resources143 (resourceSelector143_38 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_39 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        17
      else
        18
    else
      if j.val ≤ 7 then
        19
      else
        20
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        21
      else
        22
    else
      if j.val ≤ 15 then
        23
      else
        if j.val ≤ 17 then
          24
        else
          25

private theorem resourceRequirements143_143_b39 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 39 (j.val + 1)
      (resources143 (resourceSelector143_39 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_40 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        18
      else
        19
    else
      if j.val ≤ 7 then
        20
      else
        21
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        22
      else
        23
    else
      if j.val ≤ 15 then
        24
      else
        25

private theorem resourceRequirements143_143_b40 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 40 (j.val + 1)
      (resources143 (resourceSelector143_40 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_41 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        18
      else
        19
    else
      if j.val ≤ 5 then
        20
      else
        21
  else
    if j.val ≤ 11 then
      if j.val ≤ 9 then
        22
      else
        23
    else
      if j.val ≤ 13 then
        24
      else
        25

private theorem resourceRequirements143_143_b41 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 41 (j.val + 1)
      (resources143 (resourceSelector143_41 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_42 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      19
    else
      if j.val ≤ 3 then
        20
      else
        21
  else
    if j.val ≤ 9 then
      if j.val ≤ 7 then
        22
      else
        23
    else
      if j.val ≤ 11 then
        24
      else
        25

private theorem resourceRequirements143_143_b42 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 42 (j.val + 1)
      (resources143 (resourceSelector143_42 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_43 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      20
    else
      if j.val ≤ 3 then
        21
      else
        22
  else
    if j.val ≤ 7 then
      23
    else
      if j.val ≤ 9 then
        24
      else
        25

private theorem resourceRequirements143_143_b43 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 43 (j.val + 1)
      (resources143 (resourceSelector143_43 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_44 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      21
    else
      22
  else
    if j.val ≤ 5 then
      23
    else
      if j.val ≤ 7 then
        24
      else
        25

private theorem resourceRequirements143_143_b44 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 44 (j.val + 1)
      (resources143 (resourceSelector143_44 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_45 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      22
    else
      23
  else
    if j.val ≤ 5 then
      24
    else
      if j.val ≤ 21 then
        25
      else
        26

private theorem resourceRequirements143_143_b45 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 45 (j.val + 1)
      (resources143 (resourceSelector143_45 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_46 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      23
    else
      24
  else
    if j.val ≤ 19 then
      25
    else
      if j.val ≤ 21 then
        26
      else
        27

private theorem resourceRequirements143_143_b46 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 46 (j.val + 1)
      (resources143 (resourceSelector143_46 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143_47 (j : Fin 23) : Fin 28 :=
  if j.val ≤ 17 then
    if j.val ≤ 1 then
      24
    else
      25
  else
    if j.val ≤ 19 then
      26
    else
      27

private theorem resourceRequirements143_143_b47 :
    ∀ j : Fin 23, ResourceRequirements 143 [3, 5, 7, 11] 47 (j.val + 1)
      (resources143 (resourceSelector143_47 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector143 (b : Fin 48) (j : Fin 23) : Fin 28 :=
  match b.val with
  | 0 => resourceSelector143_0 j
  | 1 => resourceSelector143_1 j
  | 2 => resourceSelector143_2 j
  | 3 => resourceSelector143_3 j
  | 4 => resourceSelector143_4 j
  | 5 => resourceSelector143_5 j
  | 6 => resourceSelector143_6 j
  | 7 => resourceSelector143_7 j
  | 8 => resourceSelector143_8 j
  | 9 => resourceSelector143_9 j
  | 10 => resourceSelector143_10 j
  | 11 => resourceSelector143_11 j
  | 12 => resourceSelector143_12 j
  | 13 => resourceSelector143_13 j
  | 14 => resourceSelector143_14 j
  | 15 => resourceSelector143_15 j
  | 16 => resourceSelector143_16 j
  | 17 => resourceSelector143_17 j
  | 18 => resourceSelector143_18 j
  | 19 => resourceSelector143_19 j
  | 20 => resourceSelector143_20 j
  | 21 => resourceSelector143_21 j
  | 22 => resourceSelector143_22 j
  | 23 => resourceSelector143_23 j
  | 24 => resourceSelector143_24 j
  | 25 => resourceSelector143_25 j
  | 26 => resourceSelector143_26 j
  | 27 => resourceSelector143_27 j
  | 28 => resourceSelector143_28 j
  | 29 => resourceSelector143_29 j
  | 30 => resourceSelector143_30 j
  | 31 => resourceSelector143_31 j
  | 32 => resourceSelector143_32 j
  | 33 => resourceSelector143_33 j
  | 34 => resourceSelector143_34 j
  | 35 => resourceSelector143_35 j
  | 36 => resourceSelector143_36 j
  | 37 => resourceSelector143_37 j
  | 38 => resourceSelector143_38 j
  | 39 => resourceSelector143_39 j
  | 40 => resourceSelector143_40 j
  | 41 => resourceSelector143_41 j
  | 42 => resourceSelector143_42 j
  | 43 => resourceSelector143_43 j
  | 44 => resourceSelector143_44 j
  | 45 => resourceSelector143_45 j
  | 46 => resourceSelector143_46 j
  | _ => resourceSelector143_47 j

theorem finiteCheck143_143 : finiteIntervalCheck 143 143 smallOrder143 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 143) (U := 143) (O := smallOrder143) (ps := [3, 5, 7, 11]) resources143 resourceSelector143
  · intro i
    fin_cases i
    · exact validResource143_0
    · exact validResource143_1
    · exact validResource143_2
    · exact validResource143_3
    · exact validResource143_4
    · exact validResource143_5
    · exact validResource143_6
    · exact validResource143_7
    · exact validResource143_8
    · exact validResource143_9
    · exact validResource143_10
    · exact validResource143_11
    · exact validResource143_12
    · exact validResource143_13
    · exact validResource143_14
    · exact validResource143_15
    · exact validResource143_16
    · exact validResource143_17
    · exact validResource143_18
    · exact validResource143_19
    · exact validResource143_20
    · exact validResource143_21
    · exact validResource143_22
    · exact validResource143_23
    · exact validResource143_24
    · exact validResource143_25
    · exact validResource143_26
    · exact validResource143_27
  · intro b j
    fin_cases b
    · exact resourceRequirements143_143_b0 j
    · exact resourceRequirements143_143_b1 j
    · exact resourceRequirements143_143_b2 j
    · exact resourceRequirements143_143_b3 j
    · exact resourceRequirements143_143_b4 j
    · exact resourceRequirements143_143_b5 j
    · exact resourceRequirements143_143_b6 j
    · exact resourceRequirements143_143_b7 j
    · exact resourceRequirements143_143_b8 j
    · exact resourceRequirements143_143_b9 j
    · exact resourceRequirements143_143_b10 j
    · exact resourceRequirements143_143_b11 j
    · exact resourceRequirements143_143_b12 j
    · exact resourceRequirements143_143_b13 j
    · exact resourceRequirements143_143_b14 j
    · exact resourceRequirements143_143_b15 j
    · exact resourceRequirements143_143_b16 j
    · exact resourceRequirements143_143_b17 j
    · exact resourceRequirements143_143_b18 j
    · exact resourceRequirements143_143_b19 j
    · exact resourceRequirements143_143_b20 j
    · exact resourceRequirements143_143_b21 j
    · exact resourceRequirements143_143_b22 j
    · exact resourceRequirements143_143_b23 j
    · exact resourceRequirements143_143_b24 j
    · exact resourceRequirements143_143_b25 j
    · exact resourceRequirements143_143_b26 j
    · exact resourceRequirements143_143_b27 j
    · exact resourceRequirements143_143_b28 j
    · exact resourceRequirements143_143_b29 j
    · exact resourceRequirements143_143_b30 j
    · exact resourceRequirements143_143_b31 j
    · exact resourceRequirements143_143_b32 j
    · exact resourceRequirements143_143_b33 j
    · exact resourceRequirements143_143_b34 j
    · exact resourceRequirements143_143_b35 j
    · exact resourceRequirements143_143_b36 j
    · exact resourceRequirements143_143_b37 j
    · exact resourceRequirements143_143_b38 j
    · exact resourceRequirements143_143_b39 j
    · exact resourceRequirements143_143_b40 j
    · exact resourceRequirements143_143_b41 j
    · exact resourceRequirements143_143_b42 j
    · exact resourceRequirements143_143_b43 j
    · exact resourceRequirements143_143_b44 j
    · exact resourceRequirements143_143_b45 j
    · exact resourceRequirements143_143_b46 j
    · exact resourceRequirements143_143_b47 j

theorem exactCertificate143_143 : ExactIntervalCertificate 143 143 smallOrder143 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck143_143
#print axioms smallOrder143_nodup
#print axioms smallOrder143_set
#print axioms finiteCheck143_143
#print axioms exactCertificate143_143
end Erdos883Verified
