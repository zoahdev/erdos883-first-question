import Erdos883SmallCertificateSieveCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder139 : List ℕ := [1, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 121, 7, 49, 133, 119, 5, 25, 125, 91, 77, 115, 95, 85, 65, 55, 35, 3, 9, 27, 81, 129, 123, 111, 93, 87, 69, 57, 51, 39, 117, 33, 99, 21, 63, 15, 45, 75, 135, 105]
theorem smallOrder139_nodup : smallOrder139.Nodup := by decide +kernel
theorem smallOrder139_set : smallOrder139.toFinset = oddUniverse 139 := by decide +kernel

private def resources139 (i : Fin 24) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨70, 0, 23, true⟩
  | 1 => ⟨58, 0, 27, true⟩
  | 2 => ⟨54, 0, 30, true⟩
  | 3 => ⟨51, 0, 32, true⟩
  | 4 => ⟨51, 1, 34, true⟩
  | 5 => ⟨47, 0, 38, true⟩
  | 6 => ⟨43, 0, 40, true⟩
  | 7 => ⟨41, 0, 41, true⟩
  | 8 => ⟨40, 0, 44, true⟩
  | 9 => ⟨40, 2, 45, true⟩
  | 10 => ⟨39, 2, 45, true⟩
  | 11 => ⟨36, 0, 46, true⟩
  | 12 => ⟨35, 0, 47, true⟩
  | 13 => ⟨34, 0, 49, true⟩
  | 14 => ⟨32, 0, 51, true⟩
  | 15 => ⟨30, 0, 52, true⟩
  | 16 => ⟨29, 0, 53, true⟩
  | 17 => ⟨28, 0, 54, true⟩
  | 18 => ⟨27, 0, 55, true⟩
  | 19 => ⟨26, 0, 56, true⟩
  | 20 => ⟨25, 0, 57, true⟩
  | 21 => ⟨24, 0, 64, true⟩
  | 22 => ⟨17, 0, 65, true⟩
  | _ => ⟨16, 0, 69, true⟩

private def factors139 (v : ℕ) : List ℕ :=
  if v ≤ 69 then
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
      if v ≤ 51 then
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
              if v ≤ 49 then
                [7, 7]
              else
                [3, 17]
      else
        if v ≤ 59 then
          if v ≤ 55 then
            if v ≤ 53 then
              [53]
            else
              [5, 11]
          else
            if v ≤ 57 then
              [3, 19]
            else
              [59]
        else
          if v ≤ 63 then
            if v ≤ 61 then
              [61]
            else
              [3, 3, 7]
          else
            if v ≤ 65 then
              [5, 13]
            else
              if v ≤ 67 then
                [67]
              else
                [3, 23]
  else
    if v ≤ 103 then
      if v ≤ 85 then
        if v ≤ 77 then
          if v ≤ 73 then
            if v ≤ 71 then
              [71]
            else
              [73]
          else
            if v ≤ 75 then
              [3, 5, 5]
            else
              [7, 11]
        else
          if v ≤ 81 then
            if v ≤ 79 then
              [79]
            else
              [3, 3, 3, 3]
          else
            if v ≤ 83 then
              [83]
            else
              [5, 17]
      else
        if v ≤ 93 then
          if v ≤ 89 then
            if v ≤ 87 then
              [3, 29]
            else
              [89]
          else
            if v ≤ 91 then
              [7, 13]
            else
              [3, 31]
        else
          if v ≤ 97 then
            if v ≤ 95 then
              [5, 19]
            else
              [97]
          else
            if v ≤ 99 then
              [3, 3, 11]
            else
              if v ≤ 101 then
                [101]
              else
                [103]
    else
      if v ≤ 121 then
        if v ≤ 111 then
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
          if v ≤ 115 then
            if v ≤ 113 then
              [113]
            else
              [5, 23]
          else
            if v ≤ 117 then
              [3, 3, 13]
            else
              if v ≤ 119 then
                [7, 17]
              else
                [11, 11]
      else
        if v ≤ 129 then
          if v ≤ 125 then
            if v ≤ 123 then
              [3, 41]
            else
              [5, 5, 5]
          else
            if v ≤ 127 then
              [127]
            else
              [3, 43]
        else
          if v ≤ 133 then
            if v ≤ 131 then
              [131]
            else
              [7, 19]
          else
            if v ≤ 135 then
              [3, 3, 3, 5]
            else
              if v ≤ 137 then
                [137]
              else
                [139]

private theorem factorsValid139 : FactorDataValid smallOrder139 factors139 := by
  unfold FactorDataValid
  decide +kernel

private theorem validResource139_0 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 0) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_1 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 1) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_2 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 2) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_3 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 3) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_4 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 4) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_5 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 5) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_6 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 6) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_7 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 7) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_8 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 8) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_9 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 9) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_10 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 10) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_11 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 11) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_12 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 12) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_13 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 13) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_14 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 14) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_15 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 15) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_16 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 16) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_17 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 17) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_18 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 18) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_19 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 19) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_20 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 20) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_21 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 21) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_22 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 22) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private theorem validResource139_23 :
    PrefixResourceValid 139 smallOrder139 [3, 5, 7, 11] (resources139 23) := by
  apply prefixResourceValid_of_sieveCheck factorsValid139
  decide +kernel

private def resourceSelector139_0 (j : Fin 23) : Fin 24 :=
  0

private theorem resourceRequirements139_139_b0 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 0 (j.val + 1)
      (resources139 (resourceSelector139_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_1 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 21 then
    0
  else
    1

private theorem resourceRequirements139_139_b1 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 1 (j.val + 1)
      (resources139 (resourceSelector139_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_2 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 19 then
    0
  else
    1

private theorem resourceRequirements139_139_b2 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 2 (j.val + 1)
      (resources139 (resourceSelector139_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_3 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 17 then
    0
  else
    1

private theorem resourceRequirements139_139_b3 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 3 (j.val + 1)
      (resources139 (resourceSelector139_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_4 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 15 then
    0
  else
    1

private theorem resourceRequirements139_139_b4 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 4 (j.val + 1)
      (resources139 (resourceSelector139_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_5 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    0
  else
    if j.val ≤ 21 then
      1
    else
      2

private theorem resourceRequirements139_139_b5 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 5 (j.val + 1)
      (resources139 (resourceSelector139_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_6 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    0
  else
    if j.val ≤ 19 then
      1
    else
      2

private theorem resourceRequirements139_139_b6 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 6 (j.val + 1)
      (resources139 (resourceSelector139_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_7 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    0
  else
    if j.val ≤ 17 then
      1
    else
      2

private theorem resourceRequirements139_139_b7 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 7 (j.val + 1)
      (resources139 (resourceSelector139_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_8 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      0
    else
      1
  else
    if j.val ≤ 21 then
      2
    else
      3

private theorem resourceRequirements139_139_b8 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 8 (j.val + 1)
      (resources139 (resourceSelector139_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_9 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      0
    else
      1
  else
    if j.val ≤ 19 then
      2
    else
      3

private theorem resourceRequirements139_139_b9 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 9 (j.val + 1)
      (resources139 (resourceSelector139_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_10 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      0
    else
      1
  else
    if j.val ≤ 17 then
      2
    else
      if j.val ≤ 21 then
        3
      else
        4

private theorem resourceRequirements139_139_b10 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 10 (j.val + 1)
      (resources139 (resourceSelector139_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_11 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      0
    else
      1
  else
    if j.val ≤ 15 then
      2
    else
      if j.val ≤ 20 then
        3
      else
        4

private theorem resourceRequirements139_139_b11 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 11 (j.val + 1)
      (resources139 (resourceSelector139_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_12 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      1
    else
      2
  else
    if j.val ≤ 19 then
      3
    else
      if j.val ≤ 21 then
        4
      else
        5

private theorem resourceRequirements139_139_b12 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 12 (j.val + 1)
      (resources139 (resourceSelector139_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_13 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      1
    else
      2
  else
    if j.val ≤ 18 then
      3
    else
      if j.val ≤ 19 then
        4
      else
        5

private theorem resourceRequirements139_139_b13 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 13 (j.val + 1)
      (resources139 (resourceSelector139_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_14 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      1
    else
      2
  else
    if j.val ≤ 17 then
      3
    else
      5

private theorem resourceRequirements139_139_b14 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 14 (j.val + 1)
      (resources139 (resourceSelector139_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_15 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      1
    else
      2
  else
    if j.val ≤ 15 then
      3
    else
      5

private theorem resourceRequirements139_139_b15 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 15 (j.val + 1)
      (resources139 (resourceSelector139_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_16 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      2
    else
      3
  else
    if j.val ≤ 21 then
      5
    else
      6

private theorem resourceRequirements139_139_b16 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 16 (j.val + 1)
      (resources139 (resourceSelector139_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_17 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      2
    else
      3
  else
    if j.val ≤ 19 then
      5
    else
      6

private theorem resourceRequirements139_139_b17 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 17 (j.val + 1)
      (resources139 (resourceSelector139_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_18 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      2
    else
      3
  else
    if j.val ≤ 17 then
      5
    else
      if j.val ≤ 21 then
        6
      else
        7

private theorem resourceRequirements139_139_b18 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 18 (j.val + 1)
      (resources139 (resourceSelector139_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_19 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      3
    else
      5
  else
    if j.val ≤ 19 then
      6
    else
      if j.val ≤ 21 then
        7
      else
        8

private theorem resourceRequirements139_139_b19 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 19 (j.val + 1)
      (resources139 (resourceSelector139_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_20 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      3
    else
      5
  else
    if j.val ≤ 17 then
      6
    else
      if j.val ≤ 19 then
        7
      else
        8

private theorem resourceRequirements139_139_b20 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 20 (j.val + 1)
      (resources139 (resourceSelector139_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_21 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      3
    else
      5
  else
    if j.val ≤ 15 then
      6
    else
      if j.val ≤ 17 then
        7
      else
        8

private theorem resourceRequirements139_139_b21 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 21 (j.val + 1)
      (resources139 (resourceSelector139_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_22 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 1 then
      3
    else
      if j.val ≤ 9 then
        5
      else
        6
  else
    if j.val ≤ 15 then
      7
    else
      if j.val ≤ 21 then
        8
      else
        9

private theorem resourceRequirements139_139_b22 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 22 (j.val + 1)
      (resources139 (resourceSelector139_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_23 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      5
    else
      if j.val ≤ 11 then
        6
      else
        7
  else
    if j.val ≤ 20 then
      8
    else
      if j.val ≤ 21 then
        10
      else
        11

private theorem resourceRequirements139_139_b23 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 23 (j.val + 1)
      (resources139 (resourceSelector139_23 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_24 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      5
    else
      if j.val ≤ 9 then
        6
      else
        7
  else
    if j.val ≤ 19 then
      8
    else
      if j.val ≤ 21 then
        11
      else
        12

private theorem resourceRequirements139_139_b24 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 24 (j.val + 1)
      (resources139 (resourceSelector139_24 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_25 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      5
    else
      if j.val ≤ 7 then
        6
      else
        7
  else
    if j.val ≤ 19 then
      if j.val ≤ 17 then
        8
      else
        11
    else
      if j.val ≤ 21 then
        12
      else
        13

private theorem resourceRequirements139_139_b25 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 25 (j.val + 1)
      (resources139 (resourceSelector139_25 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_26 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      5
    else
      if j.val ≤ 5 then
        6
      else
        7
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        8
      else
        11
    else
      if j.val ≤ 19 then
        12
      else
        13

private theorem resourceRequirements139_139_b26 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 26 (j.val + 1)
      (resources139 (resourceSelector139_26 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_27 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      6
    else
      if j.val ≤ 5 then
        7
      else
        8
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        11
      else
        12
    else
      if j.val ≤ 21 then
        13
      else
        14

private theorem resourceRequirements139_139_b27 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 27 (j.val + 1)
      (resources139 (resourceSelector139_27 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_28 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 1 then
      6
    else
      if j.val ≤ 3 then
        7
      else
        8
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        11
      else
        12
    else
      if j.val ≤ 19 then
        13
      else
        14

private theorem resourceRequirements139_139_b28 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 28 (j.val + 1)
      (resources139 (resourceSelector139_28 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_29 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 1 then
      7
    else
      if j.val ≤ 9 then
        8
      else
        11
  else
    if j.val ≤ 17 then
      if j.val ≤ 13 then
        12
      else
        13
    else
      if j.val ≤ 21 then
        14
      else
        15

private theorem resourceRequirements139_139_b29 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 29 (j.val + 1)
      (resources139 (resourceSelector139_29 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_30 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      8
    else
      if j.val ≤ 9 then
        11
      else
        12
  else
    if j.val ≤ 19 then
      if j.val ≤ 15 then
        13
      else
        14
    else
      if j.val ≤ 21 then
        15
      else
        16

private theorem resourceRequirements139_139_b30 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 30 (j.val + 1)
      (resources139 (resourceSelector139_30 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_31 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 5 then
        8
      else
        11
    else
      if j.val ≤ 9 then
        12
      else
        13
  else
    if j.val ≤ 19 then
      if j.val ≤ 17 then
        14
      else
        15
    else
      if j.val ≤ 21 then
        16
      else
        17

private theorem resourceRequirements139_139_b31 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 31 (j.val + 1)
      (resources139 (resourceSelector139_31 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_32 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        8
      else
        11
    else
      if j.val ≤ 7 then
        12
      else
        13
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        14
      else
        15
    else
      if j.val ≤ 19 then
        16
      else
        if j.val ≤ 21 then
          17
        else
          18

private theorem resourceRequirements139_139_b32 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 32 (j.val + 1)
      (resources139 (resourceSelector139_32 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_33 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        8
      else
        11
    else
      if j.val ≤ 5 then
        12
      else
        if j.val ≤ 9 then
          13
        else
          14
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        15
      else
        16
    else
      if j.val ≤ 19 then
        17
      else
        if j.val ≤ 21 then
          18
        else
          19

private theorem resourceRequirements139_139_b33 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 33 (j.val + 1)
      (resources139 (resourceSelector139_33 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_34 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        11
      else
        12
    else
      if j.val ≤ 7 then
        13
      else
        if j.val ≤ 11 then
          14
        else
          15
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        16
      else
        17
    else
      if j.val ≤ 19 then
        18
      else
        if j.val ≤ 21 then
          19
        else
          20

private theorem resourceRequirements139_139_b34 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 34 (j.val + 1)
      (resources139 (resourceSelector139_34 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_35 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        12
      else
        13
    else
      if j.val ≤ 9 then
        14
      else
        if j.val ≤ 11 then
          15
        else
          16
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
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

private theorem resourceRequirements139_139_b35 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 35 (j.val + 1)
      (resources139 (resourceSelector139_35 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_36 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        13
      else
        14
    else
      if j.val ≤ 9 then
        15
      else
        16
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        17
      else
        18
    else
      if j.val ≤ 17 then
        19
      else
        if j.val ≤ 19 then
          20
        else
          21

private theorem resourceRequirements139_139_b36 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 36 (j.val + 1)
      (resources139 (resourceSelector139_36 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_37 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        13
      else
        14
    else
      if j.val ≤ 7 then
        15
      else
        16
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        17
      else
        18
    else
      if j.val ≤ 15 then
        19
      else
        if j.val ≤ 17 then
          20
        else
          21

private theorem resourceRequirements139_139_b37 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 37 (j.val + 1)
      (resources139 (resourceSelector139_37 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_38 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        14
      else
        15
    else
      if j.val ≤ 7 then
        16
      else
        17
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        18
      else
        19
    else
      if j.val ≤ 15 then
        20
      else
        21

private theorem resourceRequirements139_139_b38 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 38 (j.val + 1)
      (resources139 (resourceSelector139_38 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_39 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        14
      else
        15
    else
      if j.val ≤ 5 then
        16
      else
        17
  else
    if j.val ≤ 11 then
      if j.val ≤ 9 then
        18
      else
        19
    else
      if j.val ≤ 13 then
        20
      else
        21

private theorem resourceRequirements139_139_b39 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 39 (j.val + 1)
      (resources139 (resourceSelector139_39 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_40 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      15
    else
      if j.val ≤ 3 then
        16
      else
        17
  else
    if j.val ≤ 9 then
      if j.val ≤ 7 then
        18
      else
        19
    else
      if j.val ≤ 11 then
        20
      else
        21

private theorem resourceRequirements139_139_b40 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 40 (j.val + 1)
      (resources139 (resourceSelector139_40 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_41 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      16
    else
      if j.val ≤ 3 then
        17
      else
        18
  else
    if j.val ≤ 7 then
      19
    else
      if j.val ≤ 9 then
        20
      else
        21

private theorem resourceRequirements139_139_b41 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 41 (j.val + 1)
      (resources139 (resourceSelector139_41 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_42 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      17
    else
      if j.val ≤ 3 then
        18
      else
        19
  else
    if j.val ≤ 7 then
      20
    else
      if j.val ≤ 21 then
        21
      else
        22

private theorem resourceRequirements139_139_b42 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 42 (j.val + 1)
      (resources139 (resourceSelector139_42 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_43 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      18
    else
      if j.val ≤ 3 then
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

private theorem resourceRequirements139_139_b43 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 43 (j.val + 1)
      (resources139 (resourceSelector139_43 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_44 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      19
    else
      20
  else
    if j.val ≤ 17 then
      21
    else
      if j.val ≤ 19 then
        22
      else
        23

private theorem resourceRequirements139_139_b44 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 44 (j.val + 1)
      (resources139 (resourceSelector139_44 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_45 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 15 then
    if j.val ≤ 1 then
      20
    else
      21
  else
    if j.val ≤ 17 then
      22
    else
      23

private theorem resourceRequirements139_139_b45 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 45 (j.val + 1)
      (resources139 (resourceSelector139_45 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139_46 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    21
  else
    if j.val ≤ 15 then
      22
    else
      23

private theorem resourceRequirements139_139_b46 :
    ∀ j : Fin 23, ResourceRequirements 139 [3, 5, 7, 11] 46 (j.val + 1)
      (resources139 (resourceSelector139_46 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector139 (b : Fin 47) (j : Fin 23) : Fin 24 :=
  match b.val with
  | 0 => resourceSelector139_0 j
  | 1 => resourceSelector139_1 j
  | 2 => resourceSelector139_2 j
  | 3 => resourceSelector139_3 j
  | 4 => resourceSelector139_4 j
  | 5 => resourceSelector139_5 j
  | 6 => resourceSelector139_6 j
  | 7 => resourceSelector139_7 j
  | 8 => resourceSelector139_8 j
  | 9 => resourceSelector139_9 j
  | 10 => resourceSelector139_10 j
  | 11 => resourceSelector139_11 j
  | 12 => resourceSelector139_12 j
  | 13 => resourceSelector139_13 j
  | 14 => resourceSelector139_14 j
  | 15 => resourceSelector139_15 j
  | 16 => resourceSelector139_16 j
  | 17 => resourceSelector139_17 j
  | 18 => resourceSelector139_18 j
  | 19 => resourceSelector139_19 j
  | 20 => resourceSelector139_20 j
  | 21 => resourceSelector139_21 j
  | 22 => resourceSelector139_22 j
  | 23 => resourceSelector139_23 j
  | 24 => resourceSelector139_24 j
  | 25 => resourceSelector139_25 j
  | 26 => resourceSelector139_26 j
  | 27 => resourceSelector139_27 j
  | 28 => resourceSelector139_28 j
  | 29 => resourceSelector139_29 j
  | 30 => resourceSelector139_30 j
  | 31 => resourceSelector139_31 j
  | 32 => resourceSelector139_32 j
  | 33 => resourceSelector139_33 j
  | 34 => resourceSelector139_34 j
  | 35 => resourceSelector139_35 j
  | 36 => resourceSelector139_36 j
  | 37 => resourceSelector139_37 j
  | 38 => resourceSelector139_38 j
  | 39 => resourceSelector139_39 j
  | 40 => resourceSelector139_40 j
  | 41 => resourceSelector139_41 j
  | 42 => resourceSelector139_42 j
  | 43 => resourceSelector139_43 j
  | 44 => resourceSelector139_44 j
  | 45 => resourceSelector139_45 j
  | _ => resourceSelector139_46 j

theorem finiteCheck139_139 : finiteIntervalCheck 139 139 smallOrder139 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 139) (U := 139) (O := smallOrder139) (ps := [3, 5, 7, 11]) resources139 resourceSelector139
  · intro i
    fin_cases i
    · exact validResource139_0
    · exact validResource139_1
    · exact validResource139_2
    · exact validResource139_3
    · exact validResource139_4
    · exact validResource139_5
    · exact validResource139_6
    · exact validResource139_7
    · exact validResource139_8
    · exact validResource139_9
    · exact validResource139_10
    · exact validResource139_11
    · exact validResource139_12
    · exact validResource139_13
    · exact validResource139_14
    · exact validResource139_15
    · exact validResource139_16
    · exact validResource139_17
    · exact validResource139_18
    · exact validResource139_19
    · exact validResource139_20
    · exact validResource139_21
    · exact validResource139_22
    · exact validResource139_23
  · intro b j
    fin_cases b
    · exact resourceRequirements139_139_b0 j
    · exact resourceRequirements139_139_b1 j
    · exact resourceRequirements139_139_b2 j
    · exact resourceRequirements139_139_b3 j
    · exact resourceRequirements139_139_b4 j
    · exact resourceRequirements139_139_b5 j
    · exact resourceRequirements139_139_b6 j
    · exact resourceRequirements139_139_b7 j
    · exact resourceRequirements139_139_b8 j
    · exact resourceRequirements139_139_b9 j
    · exact resourceRequirements139_139_b10 j
    · exact resourceRequirements139_139_b11 j
    · exact resourceRequirements139_139_b12 j
    · exact resourceRequirements139_139_b13 j
    · exact resourceRequirements139_139_b14 j
    · exact resourceRequirements139_139_b15 j
    · exact resourceRequirements139_139_b16 j
    · exact resourceRequirements139_139_b17 j
    · exact resourceRequirements139_139_b18 j
    · exact resourceRequirements139_139_b19 j
    · exact resourceRequirements139_139_b20 j
    · exact resourceRequirements139_139_b21 j
    · exact resourceRequirements139_139_b22 j
    · exact resourceRequirements139_139_b23 j
    · exact resourceRequirements139_139_b24 j
    · exact resourceRequirements139_139_b25 j
    · exact resourceRequirements139_139_b26 j
    · exact resourceRequirements139_139_b27 j
    · exact resourceRequirements139_139_b28 j
    · exact resourceRequirements139_139_b29 j
    · exact resourceRequirements139_139_b30 j
    · exact resourceRequirements139_139_b31 j
    · exact resourceRequirements139_139_b32 j
    · exact resourceRequirements139_139_b33 j
    · exact resourceRequirements139_139_b34 j
    · exact resourceRequirements139_139_b35 j
    · exact resourceRequirements139_139_b36 j
    · exact resourceRequirements139_139_b37 j
    · exact resourceRequirements139_139_b38 j
    · exact resourceRequirements139_139_b39 j
    · exact resourceRequirements139_139_b40 j
    · exact resourceRequirements139_139_b41 j
    · exact resourceRequirements139_139_b42 j
    · exact resourceRequirements139_139_b43 j
    · exact resourceRequirements139_139_b44 j
    · exact resourceRequirements139_139_b45 j
    · exact resourceRequirements139_139_b46 j

theorem exactCertificate139_139 : ExactIntervalCertificate 139 139 smallOrder139 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck139_139
#print axioms smallOrder139_nodup
#print axioms smallOrder139_set
#print axioms finiteCheck139_139
#print axioms exactCertificate139_139
end Erdos883Verified
