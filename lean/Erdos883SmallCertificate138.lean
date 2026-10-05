import Erdos883SmallCertificateSieveCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder138 : List ℕ := [1, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 121, 7, 49, 133, 119, 5, 25, 125, 91, 77, 115, 95, 85, 65, 55, 35, 3, 9, 27, 81, 129, 123, 111, 93, 87, 69, 57, 51, 39, 117, 33, 99, 21, 63, 15, 45, 75, 135, 105]
theorem smallOrder138_nodup : smallOrder138.Nodup := by decide +kernel
theorem smallOrder138_set : smallOrder138.toFinset = oddUniverse 138 := by decide +kernel

private def resources138 (i : Fin 24) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨69, 0, 23, true⟩
  | 1 => ⟨57, 0, 27, true⟩
  | 2 => ⟨53, 0, 30, true⟩
  | 3 => ⟨50, 0, 32, true⟩
  | 4 => ⟨50, 1, 34, true⟩
  | 5 => ⟨46, 0, 38, true⟩
  | 6 => ⟨42, 0, 40, true⟩
  | 7 => ⟨40, 0, 41, true⟩
  | 8 => ⟨39, 0, 44, true⟩
  | 9 => ⟨39, 2, 45, true⟩
  | 10 => ⟨38, 2, 45, true⟩
  | 11 => ⟨35, 0, 46, true⟩
  | 12 => ⟨34, 0, 47, true⟩
  | 13 => ⟨33, 0, 49, true⟩
  | 14 => ⟨31, 0, 51, true⟩
  | 15 => ⟨29, 0, 52, true⟩
  | 16 => ⟨28, 0, 53, true⟩
  | 17 => ⟨27, 0, 54, true⟩
  | 18 => ⟨26, 0, 55, true⟩
  | 19 => ⟨25, 0, 56, true⟩
  | 20 => ⟨24, 0, 57, true⟩
  | 21 => ⟨23, 0, 64, true⟩
  | 22 => ⟨16, 0, 65, true⟩
  | _ => ⟨15, 0, 68, true⟩

private def factors138 (v : ℕ) : List ℕ :=
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

private theorem factorsValid138 : FactorDataValid smallOrder138 factors138 := by
  unfold FactorDataValid
  decide +kernel

private theorem validResource138_0 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 0) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_1 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 1) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_2 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 2) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_3 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 3) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_4 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 4) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_5 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 5) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_6 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 6) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_7 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 7) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_8 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 8) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_9 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 9) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_10 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 10) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_11 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 11) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_12 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 12) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_13 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 13) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_14 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 14) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_15 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 15) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_16 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 16) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_17 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 17) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_18 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 18) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_19 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 19) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_20 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 20) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_21 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 21) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_22 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 22) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private theorem validResource138_23 :
    PrefixResourceValid 138 smallOrder138 [3, 5, 7, 11] (resources138 23) := by
  apply prefixResourceValid_of_sieveCheck factorsValid138
  decide +kernel

private def resourceSelector138_0 (j : Fin 23) : Fin 24 :=
  0

private theorem resourceRequirements138_138_b0 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 0 (j.val + 1)
      (resources138 (resourceSelector138_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_1 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 21 then
    0
  else
    1

private theorem resourceRequirements138_138_b1 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 1 (j.val + 1)
      (resources138 (resourceSelector138_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_2 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 19 then
    0
  else
    1

private theorem resourceRequirements138_138_b2 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 2 (j.val + 1)
      (resources138 (resourceSelector138_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_3 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 17 then
    0
  else
    1

private theorem resourceRequirements138_138_b3 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 3 (j.val + 1)
      (resources138 (resourceSelector138_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_4 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 15 then
    0
  else
    1

private theorem resourceRequirements138_138_b4 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 4 (j.val + 1)
      (resources138 (resourceSelector138_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_5 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 13 then
    0
  else
    if j.val ≤ 21 then
      1
    else
      2

private theorem resourceRequirements138_138_b5 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 5 (j.val + 1)
      (resources138 (resourceSelector138_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_6 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 11 then
    0
  else
    if j.val ≤ 19 then
      1
    else
      2

private theorem resourceRequirements138_138_b6 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 6 (j.val + 1)
      (resources138 (resourceSelector138_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_7 (j : Fin 23) : Fin 24 :=
  if j.val ≤ 9 then
    0
  else
    if j.val ≤ 17 then
      1
    else
      2

private theorem resourceRequirements138_138_b7 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 7 (j.val + 1)
      (resources138 (resourceSelector138_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_8 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b8 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 8 (j.val + 1)
      (resources138 (resourceSelector138_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_9 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b9 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 9 (j.val + 1)
      (resources138 (resourceSelector138_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_10 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b10 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 10 (j.val + 1)
      (resources138 (resourceSelector138_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_11 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b11 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 11 (j.val + 1)
      (resources138 (resourceSelector138_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_12 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b12 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 12 (j.val + 1)
      (resources138 (resourceSelector138_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_13 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b13 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 13 (j.val + 1)
      (resources138 (resourceSelector138_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_14 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b14 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 14 (j.val + 1)
      (resources138 (resourceSelector138_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_15 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b15 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 15 (j.val + 1)
      (resources138 (resourceSelector138_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_16 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b16 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 16 (j.val + 1)
      (resources138 (resourceSelector138_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_17 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b17 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 17 (j.val + 1)
      (resources138 (resourceSelector138_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_18 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b18 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 18 (j.val + 1)
      (resources138 (resourceSelector138_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_19 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b19 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 19 (j.val + 1)
      (resources138 (resourceSelector138_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_20 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b20 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 20 (j.val + 1)
      (resources138 (resourceSelector138_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_21 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b21 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 21 (j.val + 1)
      (resources138 (resourceSelector138_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_22 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b22 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 22 (j.val + 1)
      (resources138 (resourceSelector138_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_23 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b23 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 23 (j.val + 1)
      (resources138 (resourceSelector138_23 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_24 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b24 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 24 (j.val + 1)
      (resources138 (resourceSelector138_24 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_25 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b25 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 25 (j.val + 1)
      (resources138 (resourceSelector138_25 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_26 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b26 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 26 (j.val + 1)
      (resources138 (resourceSelector138_26 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_27 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b27 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 27 (j.val + 1)
      (resources138 (resourceSelector138_27 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_28 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b28 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 28 (j.val + 1)
      (resources138 (resourceSelector138_28 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_29 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b29 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 29 (j.val + 1)
      (resources138 (resourceSelector138_29 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_30 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b30 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 30 (j.val + 1)
      (resources138 (resourceSelector138_30 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_31 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b31 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 31 (j.val + 1)
      (resources138 (resourceSelector138_31 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_32 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b32 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 32 (j.val + 1)
      (resources138 (resourceSelector138_32 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_33 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b33 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 33 (j.val + 1)
      (resources138 (resourceSelector138_33 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_34 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b34 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 34 (j.val + 1)
      (resources138 (resourceSelector138_34 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_35 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b35 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 35 (j.val + 1)
      (resources138 (resourceSelector138_35 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_36 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b36 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 36 (j.val + 1)
      (resources138 (resourceSelector138_36 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_37 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b37 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 37 (j.val + 1)
      (resources138 (resourceSelector138_37 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_38 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b38 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 38 (j.val + 1)
      (resources138 (resourceSelector138_38 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_39 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b39 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 39 (j.val + 1)
      (resources138 (resourceSelector138_39 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_40 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b40 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 40 (j.val + 1)
      (resources138 (resourceSelector138_40 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_41 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b41 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 41 (j.val + 1)
      (resources138 (resourceSelector138_41 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_42 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b42 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 42 (j.val + 1)
      (resources138 (resourceSelector138_42 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_43 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b43 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 43 (j.val + 1)
      (resources138 (resourceSelector138_43 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_44 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b44 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 44 (j.val + 1)
      (resources138 (resourceSelector138_44 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138_45 (j : Fin 23) : Fin 24 :=
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

private theorem resourceRequirements138_138_b45 :
    ∀ j : Fin 23, ResourceRequirements 138 [3, 5, 7, 11] 45 (j.val + 1)
      (resources138 (resourceSelector138_45 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector138 (b : Fin 46) (j : Fin 23) : Fin 24 :=
  match b.val with
  | 0 => resourceSelector138_0 j
  | 1 => resourceSelector138_1 j
  | 2 => resourceSelector138_2 j
  | 3 => resourceSelector138_3 j
  | 4 => resourceSelector138_4 j
  | 5 => resourceSelector138_5 j
  | 6 => resourceSelector138_6 j
  | 7 => resourceSelector138_7 j
  | 8 => resourceSelector138_8 j
  | 9 => resourceSelector138_9 j
  | 10 => resourceSelector138_10 j
  | 11 => resourceSelector138_11 j
  | 12 => resourceSelector138_12 j
  | 13 => resourceSelector138_13 j
  | 14 => resourceSelector138_14 j
  | 15 => resourceSelector138_15 j
  | 16 => resourceSelector138_16 j
  | 17 => resourceSelector138_17 j
  | 18 => resourceSelector138_18 j
  | 19 => resourceSelector138_19 j
  | 20 => resourceSelector138_20 j
  | 21 => resourceSelector138_21 j
  | 22 => resourceSelector138_22 j
  | 23 => resourceSelector138_23 j
  | 24 => resourceSelector138_24 j
  | 25 => resourceSelector138_25 j
  | 26 => resourceSelector138_26 j
  | 27 => resourceSelector138_27 j
  | 28 => resourceSelector138_28 j
  | 29 => resourceSelector138_29 j
  | 30 => resourceSelector138_30 j
  | 31 => resourceSelector138_31 j
  | 32 => resourceSelector138_32 j
  | 33 => resourceSelector138_33 j
  | 34 => resourceSelector138_34 j
  | 35 => resourceSelector138_35 j
  | 36 => resourceSelector138_36 j
  | 37 => resourceSelector138_37 j
  | 38 => resourceSelector138_38 j
  | 39 => resourceSelector138_39 j
  | 40 => resourceSelector138_40 j
  | 41 => resourceSelector138_41 j
  | 42 => resourceSelector138_42 j
  | 43 => resourceSelector138_43 j
  | 44 => resourceSelector138_44 j
  | _ => resourceSelector138_45 j

theorem finiteCheck138_138 : finiteIntervalCheck 138 138 smallOrder138 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 138) (U := 138) (O := smallOrder138) (ps := [3, 5, 7, 11]) resources138 resourceSelector138
  · intro i
    fin_cases i
    · exact validResource138_0
    · exact validResource138_1
    · exact validResource138_2
    · exact validResource138_3
    · exact validResource138_4
    · exact validResource138_5
    · exact validResource138_6
    · exact validResource138_7
    · exact validResource138_8
    · exact validResource138_9
    · exact validResource138_10
    · exact validResource138_11
    · exact validResource138_12
    · exact validResource138_13
    · exact validResource138_14
    · exact validResource138_15
    · exact validResource138_16
    · exact validResource138_17
    · exact validResource138_18
    · exact validResource138_19
    · exact validResource138_20
    · exact validResource138_21
    · exact validResource138_22
    · exact validResource138_23
  · intro b j
    fin_cases b
    · exact resourceRequirements138_138_b0 j
    · exact resourceRequirements138_138_b1 j
    · exact resourceRequirements138_138_b2 j
    · exact resourceRequirements138_138_b3 j
    · exact resourceRequirements138_138_b4 j
    · exact resourceRequirements138_138_b5 j
    · exact resourceRequirements138_138_b6 j
    · exact resourceRequirements138_138_b7 j
    · exact resourceRequirements138_138_b8 j
    · exact resourceRequirements138_138_b9 j
    · exact resourceRequirements138_138_b10 j
    · exact resourceRequirements138_138_b11 j
    · exact resourceRequirements138_138_b12 j
    · exact resourceRequirements138_138_b13 j
    · exact resourceRequirements138_138_b14 j
    · exact resourceRequirements138_138_b15 j
    · exact resourceRequirements138_138_b16 j
    · exact resourceRequirements138_138_b17 j
    · exact resourceRequirements138_138_b18 j
    · exact resourceRequirements138_138_b19 j
    · exact resourceRequirements138_138_b20 j
    · exact resourceRequirements138_138_b21 j
    · exact resourceRequirements138_138_b22 j
    · exact resourceRequirements138_138_b23 j
    · exact resourceRequirements138_138_b24 j
    · exact resourceRequirements138_138_b25 j
    · exact resourceRequirements138_138_b26 j
    · exact resourceRequirements138_138_b27 j
    · exact resourceRequirements138_138_b28 j
    · exact resourceRequirements138_138_b29 j
    · exact resourceRequirements138_138_b30 j
    · exact resourceRequirements138_138_b31 j
    · exact resourceRequirements138_138_b32 j
    · exact resourceRequirements138_138_b33 j
    · exact resourceRequirements138_138_b34 j
    · exact resourceRequirements138_138_b35 j
    · exact resourceRequirements138_138_b36 j
    · exact resourceRequirements138_138_b37 j
    · exact resourceRequirements138_138_b38 j
    · exact resourceRequirements138_138_b39 j
    · exact resourceRequirements138_138_b40 j
    · exact resourceRequirements138_138_b41 j
    · exact resourceRequirements138_138_b42 j
    · exact resourceRequirements138_138_b43 j
    · exact resourceRequirements138_138_b44 j
    · exact resourceRequirements138_138_b45 j

theorem exactCertificate138_138 : ExactIntervalCertificate 138 138 smallOrder138 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck138_138
#print axioms smallOrder138_nodup
#print axioms smallOrder138_set
#print axioms finiteCheck138_138
#print axioms exactCertificate138_138
end Erdos883Verified
