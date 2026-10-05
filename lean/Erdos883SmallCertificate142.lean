import Erdos883SmallCertificateSieveCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder142 : List ℕ := [1, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 121, 7, 49, 133, 119, 5, 25, 125, 91, 77, 115, 95, 85, 65, 55, 35, 3, 9, 27, 81, 141, 129, 123, 111, 93, 87, 69, 57, 51, 39, 117, 33, 99, 21, 63, 15, 45, 75, 135, 105]
theorem smallOrder142_nodup : smallOrder142.Nodup := by decide +kernel
theorem smallOrder142_set : smallOrder142.toFinset = oddUniverse 142 := by decide +kernel

private def resources142 (i : Fin 24) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨71, 0, 23, true⟩
  | 1 => ⟨59, 0, 27, true⟩
  | 2 => ⟨55, 0, 31, true⟩
  | 3 => ⟨51, 0, 33, true⟩
  | 4 => ⟨51, 1, 35, true⟩
  | 5 => ⟨47, 0, 39, true⟩
  | 6 => ⟨43, 0, 41, true⟩
  | 7 => ⟨41, 0, 42, true⟩
  | 8 => ⟨40, 0, 45, true⟩
  | 9 => ⟨40, 2, 46, true⟩
  | 10 => ⟨37, 0, 92, false⟩
  | 11 => ⟨36, 0, 47, true⟩
  | 12 => ⟨35, 0, 48, true⟩
  | 13 => ⟨34, 0, 50, true⟩
  | 14 => ⟨32, 0, 52, true⟩
  | 15 => ⟨30, 0, 53, true⟩
  | 16 => ⟨29, 0, 54, true⟩
  | 17 => ⟨28, 0, 55, true⟩
  | 18 => ⟨27, 0, 56, true⟩
  | 19 => ⟨26, 0, 57, true⟩
  | 20 => ⟨25, 0, 58, true⟩
  | 21 => ⟨24, 0, 66, true⟩
  | 22 => ⟨16, 0, 67, true⟩
  | _ => ⟨15, 0, 69, true⟩

private def factors142 (v : ℕ) : List ℕ :=
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
    if v ≤ 105 then
      if v ≤ 87 then
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
              if v ≤ 85 then
                [5, 17]
              else
                [3, 29]
      else
        if v ≤ 95 then
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
          if v ≤ 99 then
            if v ≤ 97 then
              [97]
            else
              [3, 3, 11]
          else
            if v ≤ 101 then
              [101]
            else
              if v ≤ 103 then
                [103]
              else
                [3, 5, 7]
    else
      if v ≤ 123 then
        if v ≤ 113 then
          if v ≤ 109 then
            if v ≤ 107 then
              [107]
            else
              [109]
          else
            if v ≤ 111 then
              [3, 37]
            else
              [113]
        else
          if v ≤ 117 then
            if v ≤ 115 then
              [5, 23]
            else
              [3, 3, 13]
          else
            if v ≤ 119 then
              [7, 17]
            else
              if v ≤ 121 then
                [11, 11]
              else
                [3, 41]
      else
        if v ≤ 131 then
          if v ≤ 127 then
            if v ≤ 125 then
              [5, 5, 5]
            else
              [127]
          else
            if v ≤ 129 then
              [3, 43]
            else
              [131]
        else
          if v ≤ 135 then
            if v ≤ 133 then
              [7, 19]
            else
              [3, 3, 3, 5]
          else
            if v ≤ 137 then
              [137]
            else
              if v ≤ 139 then
                [139]
              else
                [3, 47]

private theorem factorsValid142 : FactorDataValid smallOrder142 factors142 := by
  unfold FactorDataValid
  decide +kernel

private theorem validResource142_0 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 0) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_1 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 1) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_2 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 2) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_3 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 3) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_4 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 4) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_5 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 5) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_6 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 6) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_7 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 7) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_8 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 8) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_9 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 9) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_10 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 10) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_11 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 11) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_12 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 12) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_13 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 13) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_14 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 14) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_15 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 15) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_16 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 16) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_17 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 17) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_18 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 18) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_19 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 19) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_20 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 20) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_21 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 21) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_22 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 22) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private theorem validResource142_23 :
    PrefixResourceValid 142 smallOrder142 [3, 5, 7, 11] (resources142 23) := by
  apply prefixResourceValid_of_sieveCheck factorsValid142
  decide +kernel

private def resourceSelector142_0 (j : Fin 23) : Fin 24 :=
  0

private theorem resourceRequirements142_142_b0 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 0 (j.val + 1)
      (resources142 (resourceSelector142_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_1 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 21 then
    0
  else
    1

private theorem resourceRequirements142_142_b1 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 1 (j.val + 1)
      (resources142 (resourceSelector142_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_2 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 19 then
    0
  else
    1

private theorem resourceRequirements142_142_b2 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 2 (j.val + 1)
      (resources142 (resourceSelector142_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_3 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 17 then
    0
  else
    1

private theorem resourceRequirements142_142_b3 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 3 (j.val + 1)
      (resources142 (resourceSelector142_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_4 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 15 then
    0
  else
    1

private theorem resourceRequirements142_142_b4 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 4 (j.val + 1)
      (resources142 (resourceSelector142_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_5 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    0
  else
    if j.val ≤ 21 then
      1
    else
      2

private theorem resourceRequirements142_142_b5 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 5 (j.val + 1)
      (resources142 (resourceSelector142_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_6 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    0
  else
    if j.val ≤ 19 then
      1
    else
      2

private theorem resourceRequirements142_142_b6 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 6 (j.val + 1)
      (resources142 (resourceSelector142_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_7 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    0
  else
    if j.val ≤ 17 then
      1
    else
      2

private theorem resourceRequirements142_142_b7 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 7 (j.val + 1)
      (resources142 (resourceSelector142_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_8 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 7 then
    0
  else
    if j.val ≤ 15 then
      1
    else
      2

private theorem resourceRequirements142_142_b8 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 8 (j.val + 1)
      (resources142 (resourceSelector142_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_9 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      0
    else
      1
  else
    if j.val ≤ 21 then
      2
    else
      3

private theorem resourceRequirements142_142_b9 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 9 (j.val + 1)
      (resources142 (resourceSelector142_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_10 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      0
    else
      1
  else
    if j.val ≤ 19 then
      2
    else
      3

private theorem resourceRequirements142_142_b10 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 10 (j.val + 1)
      (resources142 (resourceSelector142_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_11 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
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

private theorem resourceRequirements142_142_b11 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 11 (j.val + 1)
      (resources142 (resourceSelector142_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_12 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      1
    else
      2
  else
    if j.val ≤ 20 then
      3
    else
      4

private theorem resourceRequirements142_142_b12 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 12 (j.val + 1)
      (resources142 (resourceSelector142_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_13 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
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

private theorem resourceRequirements142_142_b13 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 13 (j.val + 1)
      (resources142 (resourceSelector142_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_14 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
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

private theorem resourceRequirements142_142_b14 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 14 (j.val + 1)
      (resources142 (resourceSelector142_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_15 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      1
    else
      2
  else
    if j.val ≤ 17 then
      3
    else
      5

private theorem resourceRequirements142_142_b15 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 15 (j.val + 1)
      (resources142 (resourceSelector142_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_16 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 7 then
    2
  else
    if j.val ≤ 15 then
      3
    else
      5

private theorem resourceRequirements142_142_b16 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 16 (j.val + 1)
      (resources142 (resourceSelector142_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_17 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b17 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 17 (j.val + 1)
      (resources142 (resourceSelector142_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_18 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b18 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 18 (j.val + 1)
      (resources142 (resourceSelector142_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_19 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b19 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 19 (j.val + 1)
      (resources142 (resourceSelector142_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_20 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b20 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 20 (j.val + 1)
      (resources142 (resourceSelector142_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_21 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b21 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 21 (j.val + 1)
      (resources142 (resourceSelector142_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_22 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b22 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 22 (j.val + 1)
      (resources142 (resourceSelector142_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_23 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b23 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 23 (j.val + 1)
      (resources142 (resourceSelector142_23 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_24 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b24 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 24 (j.val + 1)
      (resources142 (resourceSelector142_24 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_25 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b25 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 25 (j.val + 1)
      (resources142 (resourceSelector142_25 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_26 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b26 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 26 (j.val + 1)
      (resources142 (resourceSelector142_26 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_27 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b27 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 27 (j.val + 1)
      (resources142 (resourceSelector142_27 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_28 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b28 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 28 (j.val + 1)
      (resources142 (resourceSelector142_28 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_29 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b29 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 29 (j.val + 1)
      (resources142 (resourceSelector142_29 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_30 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b30 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 30 (j.val + 1)
      (resources142 (resourceSelector142_30 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_31 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b31 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 31 (j.val + 1)
      (resources142 (resourceSelector142_31 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_32 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b32 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 32 (j.val + 1)
      (resources142 (resourceSelector142_32 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_33 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b33 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 33 (j.val + 1)
      (resources142 (resourceSelector142_33 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_34 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b34 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 34 (j.val + 1)
      (resources142 (resourceSelector142_34 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_35 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b35 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 35 (j.val + 1)
      (resources142 (resourceSelector142_35 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_36 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b36 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 36 (j.val + 1)
      (resources142 (resourceSelector142_36 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_37 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b37 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 37 (j.val + 1)
      (resources142 (resourceSelector142_37 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_38 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b38 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 38 (j.val + 1)
      (resources142 (resourceSelector142_38 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_39 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b39 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 39 (j.val + 1)
      (resources142 (resourceSelector142_39 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_40 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b40 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 40 (j.val + 1)
      (resources142 (resourceSelector142_40 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_41 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b41 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 41 (j.val + 1)
      (resources142 (resourceSelector142_41 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_42 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements142_142_b42 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 42 (j.val + 1)
      (resources142 (resourceSelector142_42 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_43 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      17
    else
      18
  else
    if j.val ≤ 5 then
      19
    else
      if j.val ≤ 7 then
        20
      else
        21

private theorem resourceRequirements142_142_b43 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 43 (j.val + 1)
      (resources142 (resourceSelector142_43 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_44 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      18
    else
      19
  else
    if j.val ≤ 5 then
      20
    else
      if j.val ≤ 21 then
        21
      else
        22

private theorem resourceRequirements142_142_b44 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 44 (j.val + 1)
      (resources142 (resourceSelector142_44 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_45 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
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

private theorem resourceRequirements142_142_b45 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 45 (j.val + 1)
      (resources142 (resourceSelector142_45 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142_46 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 17 then
    if j.val ≤ 1 then
      20
    else
      21
  else
    if j.val ≤ 19 then
      22
    else
      23

private theorem resourceRequirements142_142_b46 :
    ∀ j : Fin 23, ResourceRequirements 142 [3, 5, 7, 11] 46 (j.val + 1)
      (resources142 (resourceSelector142_46 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector142 (b : Fin 47) (j : Fin 23) : Fin 24 :=
  match b.val with
  | 0 => resourceSelector142_0 j
  | 1 => resourceSelector142_1 j
  | 2 => resourceSelector142_2 j
  | 3 => resourceSelector142_3 j
  | 4 => resourceSelector142_4 j
  | 5 => resourceSelector142_5 j
  | 6 => resourceSelector142_6 j
  | 7 => resourceSelector142_7 j
  | 8 => resourceSelector142_8 j
  | 9 => resourceSelector142_9 j
  | 10 => resourceSelector142_10 j
  | 11 => resourceSelector142_11 j
  | 12 => resourceSelector142_12 j
  | 13 => resourceSelector142_13 j
  | 14 => resourceSelector142_14 j
  | 15 => resourceSelector142_15 j
  | 16 => resourceSelector142_16 j
  | 17 => resourceSelector142_17 j
  | 18 => resourceSelector142_18 j
  | 19 => resourceSelector142_19 j
  | 20 => resourceSelector142_20 j
  | 21 => resourceSelector142_21 j
  | 22 => resourceSelector142_22 j
  | 23 => resourceSelector142_23 j
  | 24 => resourceSelector142_24 j
  | 25 => resourceSelector142_25 j
  | 26 => resourceSelector142_26 j
  | 27 => resourceSelector142_27 j
  | 28 => resourceSelector142_28 j
  | 29 => resourceSelector142_29 j
  | 30 => resourceSelector142_30 j
  | 31 => resourceSelector142_31 j
  | 32 => resourceSelector142_32 j
  | 33 => resourceSelector142_33 j
  | 34 => resourceSelector142_34 j
  | 35 => resourceSelector142_35 j
  | 36 => resourceSelector142_36 j
  | 37 => resourceSelector142_37 j
  | 38 => resourceSelector142_38 j
  | 39 => resourceSelector142_39 j
  | 40 => resourceSelector142_40 j
  | 41 => resourceSelector142_41 j
  | 42 => resourceSelector142_42 j
  | 43 => resourceSelector142_43 j
  | 44 => resourceSelector142_44 j
  | 45 => resourceSelector142_45 j
  | _ => resourceSelector142_46 j

theorem finiteCheck142_142 : finiteIntervalCheck 142 142 smallOrder142 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 142) (U := 142) (O := smallOrder142) (ps := [3, 5, 7, 11]) resources142 resourceSelector142
  · intro i
    fin_cases i
    · exact validResource142_0
    · exact validResource142_1
    · exact validResource142_2
    · exact validResource142_3
    · exact validResource142_4
    · exact validResource142_5
    · exact validResource142_6
    · exact validResource142_7
    · exact validResource142_8
    · exact validResource142_9
    · exact validResource142_10
    · exact validResource142_11
    · exact validResource142_12
    · exact validResource142_13
    · exact validResource142_14
    · exact validResource142_15
    · exact validResource142_16
    · exact validResource142_17
    · exact validResource142_18
    · exact validResource142_19
    · exact validResource142_20
    · exact validResource142_21
    · exact validResource142_22
    · exact validResource142_23
  · intro b j
    fin_cases b
    · exact resourceRequirements142_142_b0 j
    · exact resourceRequirements142_142_b1 j
    · exact resourceRequirements142_142_b2 j
    · exact resourceRequirements142_142_b3 j
    · exact resourceRequirements142_142_b4 j
    · exact resourceRequirements142_142_b5 j
    · exact resourceRequirements142_142_b6 j
    · exact resourceRequirements142_142_b7 j
    · exact resourceRequirements142_142_b8 j
    · exact resourceRequirements142_142_b9 j
    · exact resourceRequirements142_142_b10 j
    · exact resourceRequirements142_142_b11 j
    · exact resourceRequirements142_142_b12 j
    · exact resourceRequirements142_142_b13 j
    · exact resourceRequirements142_142_b14 j
    · exact resourceRequirements142_142_b15 j
    · exact resourceRequirements142_142_b16 j
    · exact resourceRequirements142_142_b17 j
    · exact resourceRequirements142_142_b18 j
    · exact resourceRequirements142_142_b19 j
    · exact resourceRequirements142_142_b20 j
    · exact resourceRequirements142_142_b21 j
    · exact resourceRequirements142_142_b22 j
    · exact resourceRequirements142_142_b23 j
    · exact resourceRequirements142_142_b24 j
    · exact resourceRequirements142_142_b25 j
    · exact resourceRequirements142_142_b26 j
    · exact resourceRequirements142_142_b27 j
    · exact resourceRequirements142_142_b28 j
    · exact resourceRequirements142_142_b29 j
    · exact resourceRequirements142_142_b30 j
    · exact resourceRequirements142_142_b31 j
    · exact resourceRequirements142_142_b32 j
    · exact resourceRequirements142_142_b33 j
    · exact resourceRequirements142_142_b34 j
    · exact resourceRequirements142_142_b35 j
    · exact resourceRequirements142_142_b36 j
    · exact resourceRequirements142_142_b37 j
    · exact resourceRequirements142_142_b38 j
    · exact resourceRequirements142_142_b39 j
    · exact resourceRequirements142_142_b40 j
    · exact resourceRequirements142_142_b41 j
    · exact resourceRequirements142_142_b42 j
    · exact resourceRequirements142_142_b43 j
    · exact resourceRequirements142_142_b44 j
    · exact resourceRequirements142_142_b45 j
    · exact resourceRequirements142_142_b46 j

theorem exactCertificate142_142 : ExactIntervalCertificate 142 142 smallOrder142 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck142_142
#print axioms smallOrder142_nodup
#print axioms smallOrder142_set
#print axioms finiteCheck142_142
#print axioms exactCertificate142_142
end Erdos883Verified
