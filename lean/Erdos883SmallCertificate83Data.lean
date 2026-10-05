import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData83 : List CoreOddData :=
  [⟨1, [], [0, 0, 0, 0, 0]⟩,
   ⟨83, [83], [0, 0, 0, 0, 0]⟩,
   ⟨79, [79], [0, 0, 0, 0, 0]⟩,
   ⟨73, [73], [0, 0, 0, 0, 0]⟩,
   ⟨71, [71], [0, 0, 0, 0, 0]⟩,
   ⟨67, [67], [0, 0, 0, 0, 0]⟩,
   ⟨61, [61], [0, 0, 0, 0, 0]⟩,
   ⟨59, [59], [0, 0, 0, 0, 0]⟩,
   ⟨53, [53], [0, 0, 0, 0, 0]⟩,
   ⟨47, [47], [0, 0, 0, 0, 0]⟩,
   ⟨43, [43], [0, 0, 0, 0, 0]⟩,
   ⟨41, [41], [0, 0, 0, 0, 0]⟩,
   ⟨37, [37], [0, 0, 0, 0, 0]⟩,
   ⟨31, [31], [0, 0, 0, 0, 0]⟩,
   ⟨29, [29], [0, 0, 0, 0, 0]⟩,
   ⟨23, [23], [0, 0, 0, 0, 0]⟩,
   ⟨19, [19], [0, 0, 0, 0, 0]⟩,
   ⟨17, [17], [0, 0, 0, 0, 0]⟩,
   ⟨13, [13], [0, 0, 0, 0, 0]⟩,
   ⟨11, [11], [0, 0, 0, 0, 1]⟩,
   ⟨7, [7], [0, 0, 0, 1, 2]⟩,
   ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩,
   ⟨5, [5], [0, 0, 1, 2, 4]⟩,
   ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩,
   ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩,
   ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩,
   ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩,
   ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩,
   ⟨3, [3], [0, 1, 2, 4, 8]⟩,
   ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩,
   ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩,
   ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩,
   ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩,
   ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩,
   ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]

def coreResources83 (i : Fin 16) : CoreResourceData :=
  if i.val ≤ 7 then
    if i.val ≤ 3 then
      if i.val ≤ 1 then
        if i.val ≤ 0 then
          ⟨10, 0, 74, false⟩
        else
          ⟨12, 0, 38, true⟩
      else
        if i.val ≤ 2 then
          ⟨13, 0, 37, true⟩
        else
          ⟨16, 0, 36, true⟩
    else
      if i.val ≤ 5 then
        if i.val ≤ 4 then
          ⟨17, 0, 35, true⟩
        else
          ⟨19, 0, 34, true⟩
      else
        if i.val ≤ 6 then
          ⟨20, 0, 33, true⟩
        else
          ⟨22, 0, 30, true⟩
  else
    if i.val ≤ 11 then
      if i.val ≤ 9 then
        if i.val ≤ 8 then
          ⟨24, 0, 27, true⟩
        else
          ⟨25, 0, 24, true⟩
      else
        if i.val ≤ 10 then
          ⟨28, 0, 22, true⟩
        else
          ⟨32, 0, 18, true⟩
    else
      if i.val ≤ 13 then
        if i.val ≤ 12 then
          ⟨33, 0, 17, true⟩
        else
          ⟨42, 0, 16, true⟩
      else
        if i.val ≤ 14 then
          ⟨32, 1, 22, true⟩
        else
          ⟨29, 2, 24, true⟩

def coreChunks83_0 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩]

def coreChunks83_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩]

def coreChunks83_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨37, [37], [0, 0, 0, 0, 0]⟩]

def coreChunks83_3 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks83_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩]

def coreChunks83_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩]

def coreChunks83_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩]

def coreChunks83_7 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩]

def coreChunks83_8 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks83_9 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩]

def coreChunks83_10 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks83_11 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks83_12 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨69, [3, 23], [0, 1, 2, 4, 8]⟩]

def coreChunks83_13 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]

def coreChunks83_14 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks83_15 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩]

def coreSelector83_0 (j : Fin 13) : Fin 16 :=
  13

def coreSelector83_1 (j : Fin 13) : Fin 16 :=
  13

def coreSelector83_2 (j : Fin 13) : Fin 16 :=
  13

def coreSelector83_3 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 11 then
    13
  else
    12

def coreSelector83_4 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 9 then
    13
  else
    if j.val ≤ 11 then
      12
    else
      11

def coreSelector83_5 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 7 then
    13
  else
    if j.val ≤ 9 then
      12
    else
      11

def coreSelector83_6 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 7 then
    if j.val ≤ 5 then
      13
    else
      12
  else
    if j.val ≤ 11 then
      11
    else
      14

def coreSelector83_7 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 5 then
    if j.val ≤ 3 then
      13
    else
      12
  else
    if j.val ≤ 10 then
      11
    else
      14

def coreSelector83_8 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      13
    else
      12
  else
    if j.val ≤ 9 then
      11
    else
      if j.val ≤ 11 then
        14
      else
        10

def coreSelector83_9 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 8 then
    if j.val ≤ 1 then
      12
    else
      11
  else
    if j.val ≤ 9 then
      14
    else
      10

def coreSelector83_10 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 7 then
    11
  else
    if j.val ≤ 11 then
      10
    else
      15

def coreSelector83_11 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 10 then
    if j.val ≤ 5 then
      11
    else
      10
  else
    if j.val ≤ 11 then
      15
    else
      9

def coreSelector83_12 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      11
    else
      10
  else
    if j.val ≤ 11 then
      9
    else
      8

def coreSelector83_13 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      11
    else
      10
  else
    if j.val ≤ 9 then
      9
    else
      8

def coreSelector83_14 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 7 then
    if j.val ≤ 5 then
      10
    else
      9
  else
    if j.val ≤ 11 then
      8
    else
      7

def coreSelector83_15 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 5 then
    if j.val ≤ 3 then
      10
    else
      9
  else
    if j.val ≤ 9 then
      8
    else
      7

def coreSelector83_16 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      10
    else
      9
  else
    if j.val ≤ 7 then
      8
    else
      if j.val ≤ 11 then
        7
      else
        6

def coreSelector83_17 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      9
    else
      8
  else
    if j.val ≤ 9 then
      7
    else
      if j.val ≤ 11 then
        6
      else
        5

def coreSelector83_18 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      8
    else
      7
  else
    if j.val ≤ 9 then
      6
    else
      5

def coreSelector83_19 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      8
    else
      7
  else
    if j.val ≤ 7 then
      6
    else
      if j.val ≤ 11 then
        5
      else
        4

def coreSelector83_20 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 5 then
    if j.val ≤ 3 then
      7
    else
      6
  else
    if j.val ≤ 9 then
      5
    else
      if j.val ≤ 11 then
        4
      else
        3

def coreSelector83_21 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      7
    else
      6
  else
    if j.val ≤ 7 then
      5
    else
      if j.val ≤ 9 then
        4
      else
        3

def coreSelector83_22 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      6
    else
      5
  else
    if j.val ≤ 7 then
      4
    else
      3

def coreSelector83_23 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 5 then
    if j.val ≤ 3 then
      5
    else
      4
  else
    if j.val ≤ 11 then
      3
    else
      2

def coreSelector83_24 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      5
    else
      4
  else
    if j.val ≤ 9 then
      3
    else
      if j.val ≤ 11 then
        2
      else
        1

def coreSelector83_25 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      4
    else
      3
  else
    if j.val ≤ 9 then
      2
    else
      1

def coreSelector83_26 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 7 then
    if j.val ≤ 5 then
      3
    else
      2
  else
    if j.val ≤ 11 then
      1
    else
      0

def coreSelector83_27 (j : Fin 13) : Fin 16 :=
  if j.val ≤ 5 then
    if j.val ≤ 3 then
      3
    else
      2
  else
    if j.val ≤ 10 then
      1
    else
      0

def coreSelector83 (b : Fin 28) (j : Fin 13) : Fin 16 :=
  if b.val ≤ 13 then
    if b.val ≤ 6 then
      if b.val ≤ 2 then
        if b.val ≤ 0 then
          coreSelector83_0 j
        else
          if b.val ≤ 1 then
            coreSelector83_1 j
          else
            coreSelector83_2 j
      else
        if b.val ≤ 4 then
          if b.val ≤ 3 then
            coreSelector83_3 j
          else
            coreSelector83_4 j
        else
          if b.val ≤ 5 then
            coreSelector83_5 j
          else
            coreSelector83_6 j
    else
      if b.val ≤ 9 then
        if b.val ≤ 7 then
          coreSelector83_7 j
        else
          if b.val ≤ 8 then
            coreSelector83_8 j
          else
            coreSelector83_9 j
      else
        if b.val ≤ 11 then
          if b.val ≤ 10 then
            coreSelector83_10 j
          else
            coreSelector83_11 j
        else
          if b.val ≤ 12 then
            coreSelector83_12 j
          else
            coreSelector83_13 j
  else
    if b.val ≤ 20 then
      if b.val ≤ 16 then
        if b.val ≤ 14 then
          coreSelector83_14 j
        else
          if b.val ≤ 15 then
            coreSelector83_15 j
          else
            coreSelector83_16 j
      else
        if b.val ≤ 18 then
          if b.val ≤ 17 then
            coreSelector83_17 j
          else
            coreSelector83_18 j
        else
          if b.val ≤ 19 then
            coreSelector83_19 j
          else
            coreSelector83_20 j
    else
      if b.val ≤ 23 then
        if b.val ≤ 21 then
          coreSelector83_21 j
        else
          if b.val ≤ 22 then
            coreSelector83_22 j
          else
            coreSelector83_23 j
      else
        if b.val ≤ 25 then
          if b.val ≤ 24 then
            coreSelector83_24 j
          else
            coreSelector83_25 j
        else
          if b.val ≤ 26 then
            coreSelector83_26 j
          else
            coreSelector83_27 j
def coreMetadataChunks83 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]
end Erdos883Verified
