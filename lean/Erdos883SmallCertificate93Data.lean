import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData93 : List CoreOddData :=
  [⟨1, [], [0, 0, 0, 0, 0]⟩,
   ⟨89, [89], [0, 0, 0, 0, 0]⟩,
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
   ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩,
   ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩,
   ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩,
   ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩,
   ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩,
   ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩,
   ⟨3, [3], [0, 1, 2, 4, 8]⟩,
   ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩,
   ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩,
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

def coreResources93 (i : Fin 20) : CoreResourceData :=
  if i.val ≤ 9 then
    if i.val ≤ 4 then
      if i.val ≤ 1 then
        if i.val ≤ 0 then
          ⟨11, 0, 46, true⟩
        else
          ⟨12, 0, 45, true⟩
      else
        if i.val ≤ 2 then
          ⟨16, 0, 44, true⟩
        else
          if i.val ≤ 3 then
            ⟨17, 0, 43, true⟩
          else
            ⟨19, 0, 42, true⟩
    else
      if i.val ≤ 6 then
        if i.val ≤ 5 then
          ⟨20, 0, 41, true⟩
        else
          ⟨21, 0, 39, true⟩
      else
        if i.val ≤ 7 then
          ⟨23, 0, 36, true⟩
        else
          if i.val ≤ 8 then
            ⟨25, 0, 32, true⟩
          else
            ⟨26, 0, 29, true⟩
  else
    if i.val ≤ 14 then
      if i.val ≤ 11 then
        if i.val ≤ 10 then
          ⟨27, 0, 28, true⟩
        else
          ⟨28, 0, 26, true⟩
      else
        if i.val ≤ 12 then
          ⟨31, 0, 25, true⟩
        else
          if i.val ≤ 13 then
            ⟨35, 0, 22, true⟩
          else
            ⟨37, 0, 21, true⟩
    else
      if i.val ≤ 16 then
        if i.val ≤ 15 then
          ⟨41, 0, 20, true⟩
        else
          ⟨47, 0, 19, true⟩
      else
        if i.val ≤ 17 then
          ⟨34, 1, 25, true⟩
        else
          if i.val ≤ 18 then
            ⟨30, 2, 30, true⟩
          else
            ⟨32, 2, 28, true⟩

def coreChunks93_0 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩]

def coreChunks93_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨43, [43], [0, 0, 0, 0, 0]⟩]

def coreChunks93_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]

def coreChunks93_3 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks93_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks93_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩]

def coreChunks93_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩]

def coreChunks93_7 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩]

def coreChunks93_8 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks93_9 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩]

def coreChunks93_10 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩]

def coreChunks93_11 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks93_12 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks93_13 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks93_14 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩]

def coreChunks93_15 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩]

def coreChunks93_16 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]

def coreChunks93_17 (c : Fin 3) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩]
  | _ => [⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks93_18 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩]

def coreChunks93_19 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩]

def coreSelector93_0 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 11 then
    16
  else
    15

def coreSelector93_1 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 9 then
    16
  else
    15

def coreSelector93_2 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 7 then
    16
  else
    15

def coreSelector93_3 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 5 then
    16
  else
    if j.val ≤ 13 then
      15
    else
      14

def coreSelector93_4 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 3 then
    16
  else
    if j.val ≤ 11 then
      15
    else
      14

def coreSelector93_5 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      16
    else
      15
  else
    if j.val ≤ 13 then
      14
    else
      13

def coreSelector93_6 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 7 then
    15
  else
    if j.val ≤ 11 then
      14
    else
      13

def coreSelector93_7 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 5 then
    15
  else
    if j.val ≤ 9 then
      14
    else
      13

def coreSelector93_8 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      15
    else
      14
  else
    if j.val ≤ 13 then
      13
    else
      17

def coreSelector93_9 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      15
    else
      14
  else
    if j.val ≤ 12 then
      13
    else
      if j.val ≤ 13 then
        17
      else
        12

def coreSelector93_10 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 3 then
    14
  else
    if j.val ≤ 11 then
      13
    else
      12

def coreSelector93_11 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      14
    else
      13
  else
    if j.val ≤ 13 then
      12
    else
      19

def coreSelector93_12 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 7 then
    13
  else
    if j.val ≤ 12 then
      12
    else
      19

def coreSelector93_13 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      13
    else
      12
  else
    if j.val ≤ 12 then
      11
    else
      if j.val ≤ 13 then
        18
      else
        10

def coreSelector93_14 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      13
    else
      12
  else
    if j.val ≤ 11 then
      11
    else
      if j.val ≤ 13 then
        10
      else
        9

def coreSelector93_15 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      13
    else
      if j.val ≤ 7 then
        12
      else
        11
  else
    if j.val ≤ 11 then
      10
    else
      if j.val ≤ 13 then
        9
      else
        8

def coreSelector93_16 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 7 then
    if j.val ≤ 5 then
      12
    else
      11
  else
    if j.val ≤ 9 then
      10
    else
      if j.val ≤ 11 then
        9
      else
        8

def coreSelector93_17 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      12
    else
      if j.val ≤ 5 then
        11
      else
        10
  else
    if j.val ≤ 9 then
      9
    else
      if j.val ≤ 13 then
        8
      else
        7

def coreSelector93_18 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      12
    else
      if j.val ≤ 3 then
        11
      else
        10
  else
    if j.val ≤ 7 then
      9
    else
      if j.val ≤ 11 then
        8
      else
        7

def coreSelector93_19 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      11
    else
      if j.val ≤ 3 then
        10
      else
        9
  else
    if j.val ≤ 9 then
      8
    else
      if j.val ≤ 13 then
        7
      else
        6

def coreSelector93_20 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      10
    else
      if j.val ≤ 3 then
        9
      else
        8
  else
    if j.val ≤ 11 then
      7
    else
      if j.val ≤ 13 then
        6
      else
        5

def coreSelector93_21 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      9
    else
      if j.val ≤ 5 then
        8
      else
        7
  else
    if j.val ≤ 11 then
      6
    else
      if j.val ≤ 13 then
        5
      else
        4

def coreSelector93_22 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      8
    else
      7
  else
    if j.val ≤ 9 then
      6
    else
      if j.val ≤ 11 then
        5
      else
        4

def coreSelector93_23 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      8
    else
      if j.val ≤ 5 then
        7
      else
        6
  else
    if j.val ≤ 9 then
      5
    else
      if j.val ≤ 13 then
        4
      else
        3

def coreSelector93_24 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      7
    else
      if j.val ≤ 5 then
        6
      else
        5
  else
    if j.val ≤ 11 then
      4
    else
      if j.val ≤ 13 then
        3
      else
        2

def coreSelector93_25 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      7
    else
      if j.val ≤ 3 then
        6
      else
        5
  else
    if j.val ≤ 9 then
      4
    else
      if j.val ≤ 11 then
        3
      else
        2

def coreSelector93_26 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      6
    else
      5
  else
    if j.val ≤ 7 then
      4
    else
      if j.val ≤ 9 then
        3
      else
        2

def coreSelector93_27 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      5
    else
      4
  else
    if j.val ≤ 7 then
      3
    else
      2

def coreSelector93_28 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 5 then
    if j.val ≤ 3 then
      4
    else
      3
  else
    if j.val ≤ 13 then
      2
    else
      1

def coreSelector93_29 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      4
    else
      3
  else
    if j.val ≤ 11 then
      2
    else
      if j.val ≤ 13 then
        1
      else
        0

def coreSelector93_30 (j : Fin 15) : Fin 20 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      3
    else
      2
  else
    if j.val ≤ 11 then
      1
    else
      0

def coreSelector93 (b : Fin 31) (j : Fin 15) : Fin 20 :=
  if b.val ≤ 14 then
    if b.val ≤ 6 then
      if b.val ≤ 2 then
        if b.val ≤ 0 then
          coreSelector93_0 j
        else
          if b.val ≤ 1 then
            coreSelector93_1 j
          else
            coreSelector93_2 j
      else
        if b.val ≤ 4 then
          if b.val ≤ 3 then
            coreSelector93_3 j
          else
            coreSelector93_4 j
        else
          if b.val ≤ 5 then
            coreSelector93_5 j
          else
            coreSelector93_6 j
    else
      if b.val ≤ 10 then
        if b.val ≤ 8 then
          if b.val ≤ 7 then
            coreSelector93_7 j
          else
            coreSelector93_8 j
        else
          if b.val ≤ 9 then
            coreSelector93_9 j
          else
            coreSelector93_10 j
      else
        if b.val ≤ 12 then
          if b.val ≤ 11 then
            coreSelector93_11 j
          else
            coreSelector93_12 j
        else
          if b.val ≤ 13 then
            coreSelector93_13 j
          else
            coreSelector93_14 j
  else
    if b.val ≤ 22 then
      if b.val ≤ 18 then
        if b.val ≤ 16 then
          if b.val ≤ 15 then
            coreSelector93_15 j
          else
            coreSelector93_16 j
        else
          if b.val ≤ 17 then
            coreSelector93_17 j
          else
            coreSelector93_18 j
      else
        if b.val ≤ 20 then
          if b.val ≤ 19 then
            coreSelector93_19 j
          else
            coreSelector93_20 j
        else
          if b.val ≤ 21 then
            coreSelector93_21 j
          else
            coreSelector93_22 j
    else
      if b.val ≤ 26 then
        if b.val ≤ 24 then
          if b.val ≤ 23 then
            coreSelector93_23 j
          else
            coreSelector93_24 j
        else
          if b.val ≤ 25 then
            coreSelector93_25 j
          else
            coreSelector93_26 j
      else
        if b.val ≤ 28 then
          if b.val ≤ 27 then
            coreSelector93_27 j
          else
            coreSelector93_28 j
        else
          if b.val ≤ 29 then
            coreSelector93_29 j
          else
            coreSelector93_30 j
def coreMetadataChunks93 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]
end Erdos883Verified
