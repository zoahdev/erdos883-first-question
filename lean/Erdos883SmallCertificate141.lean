import Erdos883SmallCertificateSieveCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder141 : List ℕ := [1, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 121, 7, 49, 133, 119, 5, 25, 125, 91, 77, 115, 95, 85, 65, 55, 35, 3, 9, 27, 81, 141, 129, 123, 111, 93, 87, 69, 57, 51, 39, 117, 33, 99, 21, 63, 15, 45, 75, 135, 105]
theorem smallOrder141_nodup : smallOrder141.Nodup := by decide +kernel
theorem smallOrder141_set : smallOrder141.toFinset = oddUniverse 141 := by decide +kernel

private def resources141 (i : Fin 26) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨71, 0, 23, true⟩
  | 1 => ⟨59, 0, 27, true⟩
  | 2 => ⟨55, 0, 31, true⟩
  | 3 => ⟨51, 0, 32, true⟩
  | 4 => ⟨52, 1, 35, true⟩
  | 5 => ⟨47, 0, 39, true⟩
  | 6 => ⟨43, 0, 40, true⟩
  | 7 => ⟨45, 2, 41, true⟩
  | 8 => ⟨44, 2, 46, true⟩
  | 9 => ⟨41, 0, 42, true⟩
  | 10 => ⟨40, 0, 44, true⟩
  | 11 => ⟨37, 0, 91, false⟩
  | 12 => ⟨39, 2, 46, true⟩
  | 13 => ⟨36, 0, 47, true⟩
  | 14 => ⟨35, 0, 48, true⟩
  | 15 => ⟨34, 0, 50, true⟩
  | 16 => ⟨32, 0, 52, true⟩
  | 17 => ⟨30, 0, 53, true⟩
  | 18 => ⟨29, 0, 54, true⟩
  | 19 => ⟨28, 0, 55, true⟩
  | 20 => ⟨27, 0, 56, true⟩
  | 21 => ⟨26, 0, 57, true⟩
  | 22 => ⟨25, 0, 58, true⟩
  | 23 => ⟨24, 0, 65, true⟩
  | 24 => ⟨17, 0, 66, true⟩
  | _ => ⟨16, 0, 69, true⟩

private def factors141 (v : ℕ) : List ℕ :=
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

private theorem factorsValid141 : FactorDataValid smallOrder141 factors141 := by
  unfold FactorDataValid
  decide +kernel

private theorem validResource141_0 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 0) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_1 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 1) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_2 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 2) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_3 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 3) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_4 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 4) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_5 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 5) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_6 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 6) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_7 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 7) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_8 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 8) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_9 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 9) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_10 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 10) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_11 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 11) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_12 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 12) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_13 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 13) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_14 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 14) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_15 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 15) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_16 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 16) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_17 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 17) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_18 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 18) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_19 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 19) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_20 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 20) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_21 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 21) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_22 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 22) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_23 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 23) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_24 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 24) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private theorem validResource141_25 :
    PrefixResourceValid 141 smallOrder141 [3, 5, 7, 11] (resources141 25) := by
  apply prefixResourceValid_of_sieveCheck factorsValid141
  decide +kernel

private def resourceSelector141_0 (j : Fin 23) : Fin 26 :=
  0

private theorem resourceRequirements141_141_b0 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 0 (j.val + 1)
      (resources141 (resourceSelector141_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_1 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 21 then
    0
  else
    1

private theorem resourceRequirements141_141_b1 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 1 (j.val + 1)
      (resources141 (resourceSelector141_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_2 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 19 then
    0
  else
    1

private theorem resourceRequirements141_141_b2 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 2 (j.val + 1)
      (resources141 (resourceSelector141_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_3 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 17 then
    0
  else
    1

private theorem resourceRequirements141_141_b3 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 3 (j.val + 1)
      (resources141 (resourceSelector141_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_4 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 15 then
    0
  else
    1

private theorem resourceRequirements141_141_b4 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 4 (j.val + 1)
      (resources141 (resourceSelector141_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_5 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 13 then
    0
  else
    if j.val ≤ 21 then
      1
    else
      2

private theorem resourceRequirements141_141_b5 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 5 (j.val + 1)
      (resources141 (resourceSelector141_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_6 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 11 then
    0
  else
    if j.val ≤ 19 then
      1
    else
      2

private theorem resourceRequirements141_141_b6 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 6 (j.val + 1)
      (resources141 (resourceSelector141_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_7 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 9 then
    0
  else
    if j.val ≤ 17 then
      1
    else
      2

private theorem resourceRequirements141_141_b7 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 7 (j.val + 1)
      (resources141 (resourceSelector141_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_8 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 7 then
    0
  else
    if j.val ≤ 15 then
      1
    else
      2

private theorem resourceRequirements141_141_b8 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 8 (j.val + 1)
      (resources141 (resourceSelector141_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_9 (j : Fin 23) : Fin 26 :=
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

private theorem resourceRequirements141_141_b9 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 9 (j.val + 1)
      (resources141 (resourceSelector141_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_10 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      0
    else
      1
  else
    if j.val ≤ 19 then
      2
    else
      if j.val ≤ 21 then
        3
      else
        4

private theorem resourceRequirements141_141_b10 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 10 (j.val + 1)
      (resources141 (resourceSelector141_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_11 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      0
    else
      1
  else
    if j.val ≤ 17 then
      2
    else
      if j.val ≤ 20 then
        3
      else
        4

private theorem resourceRequirements141_141_b11 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 11 (j.val + 1)
      (resources141 (resourceSelector141_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_12 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      1
    else
      2
  else
    if j.val ≤ 19 then
      3
    else
      4

private theorem resourceRequirements141_141_b12 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 12 (j.val + 1)
      (resources141 (resourceSelector141_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_13 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      1
    else
      2
  else
    if j.val ≤ 18 then
      3
    else
      if j.val ≤ 21 then
        4
      else
        5

private theorem resourceRequirements141_141_b13 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 13 (j.val + 1)
      (resources141 (resourceSelector141_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_14 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      1
    else
      2
  else
    if j.val ≤ 17 then
      3
    else
      if j.val ≤ 19 then
        4
      else
        5

private theorem resourceRequirements141_141_b14 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 14 (j.val + 1)
      (resources141 (resourceSelector141_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_15 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      1
    else
      2
  else
    if j.val ≤ 16 then
      3
    else
      if j.val ≤ 17 then
        4
      else
        5

private theorem resourceRequirements141_141_b15 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 15 (j.val + 1)
      (resources141 (resourceSelector141_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_16 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 7 then
    2
  else
    if j.val ≤ 15 then
      3
    else
      5

private theorem resourceRequirements141_141_b16 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 16 (j.val + 1)
      (resources141 (resourceSelector141_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_17 (j : Fin 23) : Fin 26 :=
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

private theorem resourceRequirements141_141_b17 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 17 (j.val + 1)
      (resources141 (resourceSelector141_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_18 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      2
    else
      3
  else
    if j.val ≤ 19 then
      5
    else
      if j.val ≤ 21 then
        6
      else
        7

private theorem resourceRequirements141_141_b18 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 18 (j.val + 1)
      (resources141 (resourceSelector141_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_19 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 17 then
    if j.val ≤ 1 then
      2
    else
      if j.val ≤ 9 then
        3
      else
        5
  else
    if j.val ≤ 20 then
      6
    else
      if j.val ≤ 21 then
        8
      else
        9

private theorem resourceRequirements141_141_b19 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 19 (j.val + 1)
      (resources141 (resourceSelector141_19 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_20 (j : Fin 23) : Fin 26 :=
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
        9
      else
        10

private theorem resourceRequirements141_141_b20 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 20 (j.val + 1)
      (resources141 (resourceSelector141_20 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_21 (j : Fin 23) : Fin 26 :=
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
        9
      else
        10

private theorem resourceRequirements141_141_b21 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 21 (j.val + 1)
      (resources141 (resourceSelector141_21 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_22 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 15 then
    if j.val ≤ 3 then
      3
    else
      if j.val ≤ 11 then
        5
      else
        6
  else
    if j.val ≤ 17 then
      9
    else
      if j.val ≤ 21 then
        10
      else
        8

private theorem resourceRequirements141_141_b22 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 22 (j.val + 1)
      (resources141 (resourceSelector141_22 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_23 (j : Fin 23) : Fin 26 :=
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
      9
    else
      if j.val ≤ 20 then
        10
      else
        8

private theorem resourceRequirements141_141_b23 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 23 (j.val + 1)
      (resources141 (resourceSelector141_23 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_24 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      5
    else
      if j.val ≤ 11 then
        6
      else
        9
  else
    if j.val ≤ 20 then
      if j.val ≤ 19 then
        10
      else
        11
    else
      if j.val ≤ 21 then
        12
      else
        13

private theorem resourceRequirements141_141_b24 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 24 (j.val + 1)
      (resources141 (resourceSelector141_24 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_25 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      5
    else
      if j.val ≤ 9 then
        6
      else
        9
  else
    if j.val ≤ 19 then
      if j.val ≤ 18 then
        10
      else
        11
    else
      if j.val ≤ 21 then
        13
      else
        14

private theorem resourceRequirements141_141_b25 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 25 (j.val + 1)
      (resources141 (resourceSelector141_25 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_26 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      5
    else
      if j.val ≤ 7 then
        6
      else
        9
  else
    if j.val ≤ 19 then
      if j.val ≤ 17 then
        10
      else
        13
    else
      if j.val ≤ 21 then
        14
      else
        15

private theorem resourceRequirements141_141_b26 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 26 (j.val + 1)
      (resources141 (resourceSelector141_26 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_27 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      5
    else
      if j.val ≤ 5 then
        6
      else
        9
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        10
      else
        13
    else
      if j.val ≤ 19 then
        14
      else
        15

private theorem resourceRequirements141_141_b27 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 27 (j.val + 1)
      (resources141 (resourceSelector141_27 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_28 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      6
    else
      if j.val ≤ 5 then
        9
      else
        10
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        13
      else
        14
    else
      if j.val ≤ 21 then
        15
      else
        16

private theorem resourceRequirements141_141_b28 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 28 (j.val + 1)
      (resources141 (resourceSelector141_28 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_29 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 11 then
    if j.val ≤ 1 then
      6
    else
      if j.val ≤ 3 then
        9
      else
        10
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        13
      else
        14
    else
      if j.val ≤ 19 then
        15
      else
        16

private theorem resourceRequirements141_141_b29 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 29 (j.val + 1)
      (resources141 (resourceSelector141_29 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_30 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 11 then
    if j.val ≤ 1 then
      9
    else
      if j.val ≤ 9 then
        10
      else
        13
  else
    if j.val ≤ 17 then
      if j.val ≤ 13 then
        14
      else
        15
    else
      if j.val ≤ 21 then
        16
      else
        17

private theorem resourceRequirements141_141_b30 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 30 (j.val + 1)
      (resources141 (resourceSelector141_30 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_31 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      10
    else
      if j.val ≤ 9 then
        13
      else
        14
  else
    if j.val ≤ 19 then
      if j.val ≤ 15 then
        15
      else
        16
    else
      if j.val ≤ 21 then
        17
      else
        18

private theorem resourceRequirements141_141_b31 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 31 (j.val + 1)
      (resources141 (resourceSelector141_31 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_32 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 5 then
        10
      else
        13
    else
      if j.val ≤ 9 then
        14
      else
        15
  else
    if j.val ≤ 19 then
      if j.val ≤ 17 then
        16
      else
        17
    else
      if j.val ≤ 21 then
        18
      else
        19

private theorem resourceRequirements141_141_b32 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 32 (j.val + 1)
      (resources141 (resourceSelector141_32 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_33 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        10
      else
        13
    else
      if j.val ≤ 7 then
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

private theorem resourceRequirements141_141_b33 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 33 (j.val + 1)
      (resources141 (resourceSelector141_33 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_34 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        10
      else
        13
    else
      if j.val ≤ 5 then
        14
      else
        if j.val ≤ 9 then
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

private theorem resourceRequirements141_141_b34 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 34 (j.val + 1)
      (resources141 (resourceSelector141_34 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_35 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        13
      else
        14
    else
      if j.val ≤ 7 then
        15
      else
        if j.val ≤ 11 then
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

private theorem resourceRequirements141_141_b35 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 35 (j.val + 1)
      (resources141 (resourceSelector141_35 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_36 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        14
      else
        15
    else
      if j.val ≤ 9 then
        16
      else
        if j.val ≤ 11 then
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

private theorem resourceRequirements141_141_b36 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 36 (j.val + 1)
      (resources141 (resourceSelector141_36 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_37 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        15
      else
        16
    else
      if j.val ≤ 9 then
        17
      else
        18
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
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

private theorem resourceRequirements141_141_b37 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 37 (j.val + 1)
      (resources141 (resourceSelector141_37 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_38 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        15
      else
        16
    else
      if j.val ≤ 7 then
        17
      else
        18
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        19
      else
        20
    else
      if j.val ≤ 15 then
        21
      else
        if j.val ≤ 17 then
          22
        else
          23

private theorem resourceRequirements141_141_b38 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 38 (j.val + 1)
      (resources141 (resourceSelector141_38 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_39 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        16
      else
        17
    else
      if j.val ≤ 7 then
        18
      else
        19
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        20
      else
        21
    else
      if j.val ≤ 15 then
        22
      else
        23

private theorem resourceRequirements141_141_b39 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 39 (j.val + 1)
      (resources141 (resourceSelector141_39 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_40 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        16
      else
        17
    else
      if j.val ≤ 5 then
        18
      else
        19
  else
    if j.val ≤ 11 then
      if j.val ≤ 9 then
        20
      else
        21
    else
      if j.val ≤ 13 then
        22
      else
        23

private theorem resourceRequirements141_141_b40 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 40 (j.val + 1)
      (resources141 (resourceSelector141_40 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_41 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      17
    else
      if j.val ≤ 3 then
        18
      else
        19
  else
    if j.val ≤ 9 then
      if j.val ≤ 7 then
        20
      else
        21
    else
      if j.val ≤ 11 then
        22
      else
        23

private theorem resourceRequirements141_141_b41 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 41 (j.val + 1)
      (resources141 (resourceSelector141_41 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_42 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      18
    else
      if j.val ≤ 3 then
        19
      else
        20
  else
    if j.val ≤ 7 then
      21
    else
      if j.val ≤ 9 then
        22
      else
        23

private theorem resourceRequirements141_141_b42 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 42 (j.val + 1)
      (resources141 (resourceSelector141_42 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_43 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      19
    else
      if j.val ≤ 3 then
        20
      else
        21
  else
    if j.val ≤ 7 then
      22
    else
      if j.val ≤ 21 then
        23
      else
        24

private theorem resourceRequirements141_141_b43 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 43 (j.val + 1)
      (resources141 (resourceSelector141_43 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_44 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      20
    else
      if j.val ≤ 3 then
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

private theorem resourceRequirements141_141_b44 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 44 (j.val + 1)
      (resources141 (resourceSelector141_44 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_45 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
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

private theorem resourceRequirements141_141_b45 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 45 (j.val + 1)
      (resources141 (resourceSelector141_45 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141_46 (j : Fin 23) : Fin 26 :=
  if j.val ≤ 15 then
    if j.val ≤ 1 then
      22
    else
      23
  else
    if j.val ≤ 17 then
      24
    else
      25

private theorem resourceRequirements141_141_b46 :
    ∀ j : Fin 23, ResourceRequirements 141 [3, 5, 7, 11] 46 (j.val + 1)
      (resources141 (resourceSelector141_46 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector141 (b : Fin 47) (j : Fin 23) : Fin 26 :=
  match b.val with
  | 0 => resourceSelector141_0 j
  | 1 => resourceSelector141_1 j
  | 2 => resourceSelector141_2 j
  | 3 => resourceSelector141_3 j
  | 4 => resourceSelector141_4 j
  | 5 => resourceSelector141_5 j
  | 6 => resourceSelector141_6 j
  | 7 => resourceSelector141_7 j
  | 8 => resourceSelector141_8 j
  | 9 => resourceSelector141_9 j
  | 10 => resourceSelector141_10 j
  | 11 => resourceSelector141_11 j
  | 12 => resourceSelector141_12 j
  | 13 => resourceSelector141_13 j
  | 14 => resourceSelector141_14 j
  | 15 => resourceSelector141_15 j
  | 16 => resourceSelector141_16 j
  | 17 => resourceSelector141_17 j
  | 18 => resourceSelector141_18 j
  | 19 => resourceSelector141_19 j
  | 20 => resourceSelector141_20 j
  | 21 => resourceSelector141_21 j
  | 22 => resourceSelector141_22 j
  | 23 => resourceSelector141_23 j
  | 24 => resourceSelector141_24 j
  | 25 => resourceSelector141_25 j
  | 26 => resourceSelector141_26 j
  | 27 => resourceSelector141_27 j
  | 28 => resourceSelector141_28 j
  | 29 => resourceSelector141_29 j
  | 30 => resourceSelector141_30 j
  | 31 => resourceSelector141_31 j
  | 32 => resourceSelector141_32 j
  | 33 => resourceSelector141_33 j
  | 34 => resourceSelector141_34 j
  | 35 => resourceSelector141_35 j
  | 36 => resourceSelector141_36 j
  | 37 => resourceSelector141_37 j
  | 38 => resourceSelector141_38 j
  | 39 => resourceSelector141_39 j
  | 40 => resourceSelector141_40 j
  | 41 => resourceSelector141_41 j
  | 42 => resourceSelector141_42 j
  | 43 => resourceSelector141_43 j
  | 44 => resourceSelector141_44 j
  | 45 => resourceSelector141_45 j
  | _ => resourceSelector141_46 j

theorem finiteCheck141_141 : finiteIntervalCheck 141 141 smallOrder141 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 141) (U := 141) (O := smallOrder141) (ps := [3, 5, 7, 11]) resources141 resourceSelector141
  · intro i
    fin_cases i
    · exact validResource141_0
    · exact validResource141_1
    · exact validResource141_2
    · exact validResource141_3
    · exact validResource141_4
    · exact validResource141_5
    · exact validResource141_6
    · exact validResource141_7
    · exact validResource141_8
    · exact validResource141_9
    · exact validResource141_10
    · exact validResource141_11
    · exact validResource141_12
    · exact validResource141_13
    · exact validResource141_14
    · exact validResource141_15
    · exact validResource141_16
    · exact validResource141_17
    · exact validResource141_18
    · exact validResource141_19
    · exact validResource141_20
    · exact validResource141_21
    · exact validResource141_22
    · exact validResource141_23
    · exact validResource141_24
    · exact validResource141_25
  · intro b j
    fin_cases b
    · exact resourceRequirements141_141_b0 j
    · exact resourceRequirements141_141_b1 j
    · exact resourceRequirements141_141_b2 j
    · exact resourceRequirements141_141_b3 j
    · exact resourceRequirements141_141_b4 j
    · exact resourceRequirements141_141_b5 j
    · exact resourceRequirements141_141_b6 j
    · exact resourceRequirements141_141_b7 j
    · exact resourceRequirements141_141_b8 j
    · exact resourceRequirements141_141_b9 j
    · exact resourceRequirements141_141_b10 j
    · exact resourceRequirements141_141_b11 j
    · exact resourceRequirements141_141_b12 j
    · exact resourceRequirements141_141_b13 j
    · exact resourceRequirements141_141_b14 j
    · exact resourceRequirements141_141_b15 j
    · exact resourceRequirements141_141_b16 j
    · exact resourceRequirements141_141_b17 j
    · exact resourceRequirements141_141_b18 j
    · exact resourceRequirements141_141_b19 j
    · exact resourceRequirements141_141_b20 j
    · exact resourceRequirements141_141_b21 j
    · exact resourceRequirements141_141_b22 j
    · exact resourceRequirements141_141_b23 j
    · exact resourceRequirements141_141_b24 j
    · exact resourceRequirements141_141_b25 j
    · exact resourceRequirements141_141_b26 j
    · exact resourceRequirements141_141_b27 j
    · exact resourceRequirements141_141_b28 j
    · exact resourceRequirements141_141_b29 j
    · exact resourceRequirements141_141_b30 j
    · exact resourceRequirements141_141_b31 j
    · exact resourceRequirements141_141_b32 j
    · exact resourceRequirements141_141_b33 j
    · exact resourceRequirements141_141_b34 j
    · exact resourceRequirements141_141_b35 j
    · exact resourceRequirements141_141_b36 j
    · exact resourceRequirements141_141_b37 j
    · exact resourceRequirements141_141_b38 j
    · exact resourceRequirements141_141_b39 j
    · exact resourceRequirements141_141_b40 j
    · exact resourceRequirements141_141_b41 j
    · exact resourceRequirements141_141_b42 j
    · exact resourceRequirements141_141_b43 j
    · exact resourceRequirements141_141_b44 j
    · exact resourceRequirements141_141_b45 j
    · exact resourceRequirements141_141_b46 j

theorem exactCertificate141_141 : ExactIntervalCertificate 141 141 smallOrder141 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck141_141
#print axioms smallOrder141_nodup
#print axioms smallOrder141_set
#print axioms finiteCheck141_141
#print axioms exactCertificate141_141
end Erdos883Verified
