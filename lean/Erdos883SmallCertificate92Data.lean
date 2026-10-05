import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData92 : List CoreOddData :=
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

def coreResources92 (i : Fin 21) : CoreResourceData :=
  if i.val ≤ 9 then
    if i.val ≤ 4 then
      if i.val ≤ 1 then
        if i.val ≤ 0 then
          ⟨11, 0, 82, false⟩
        else
          ⟨12, 0, 42, true⟩
      else
        if i.val ≤ 2 then
          ⟨13, 0, 41, true⟩
        else
          if i.val ≤ 3 then
            ⟨17, 0, 40, true⟩
          else
            ⟨18, 0, 39, true⟩
    else
      if i.val ≤ 6 then
        if i.val ≤ 5 then
          ⟨19, 0, 38, true⟩
        else
          ⟨20, 0, 37, true⟩
      else
        if i.val ≤ 7 then
          ⟨21, 0, 36, true⟩
        else
          if i.val ≤ 8 then
            ⟨23, 0, 33, true⟩
          else
            ⟨25, 0, 29, true⟩
  else
    if i.val ≤ 14 then
      if i.val ≤ 11 then
        if i.val ≤ 10 then
          ⟨27, 0, 26, true⟩
        else
          ⟨28, 0, 24, true⟩
      else
        if i.val ≤ 12 then
          ⟨31, 0, 23, true⟩
        else
          if i.val ≤ 13 then
            ⟨35, 0, 19, true⟩
          else
            ⟨37, 0, 18, true⟩
    else
      if i.val ≤ 17 then
        if i.val ≤ 15 then
          ⟨46, 0, 17, true⟩
        else
          if i.val ≤ 16 then
            ⟨36, 1, 23, true⟩
          else
            ⟨28, 2, 30, true⟩
      else
        if i.val ≤ 18 then
          ⟨29, 2, 29, true⟩
        else
          if i.val ≤ 19 then
            ⟨30, 2, 28, true⟩
          else
            ⟨33, 2, 26, true⟩

def coreChunks92_0 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩]

def coreChunks92_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩]

def coreChunks92_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨41, [41], [0, 0, 0, 0, 0]⟩]

def coreChunks92_3 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks92_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩]

def coreChunks92_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks92_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩]

def coreChunks92_7 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩]

def coreChunks92_8 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩]

def coreChunks92_9 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks92_10 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩]

def coreChunks92_11 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks92_12 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks92_13 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks92_14 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩]

def coreChunks92_15 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]

def coreChunks92_16 (c : Fin 3) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩]
  | _ => [⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩]

def coreChunks92_17 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks92_18 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩]

def coreChunks92_19 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨55, [5, 11], [0, 0, 1, 2, 5]⟩]

def coreChunks92_20 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩]

def coreSelector92_0 (j : Fin 15) : Fin 21 :=
  15

def coreSelector92_1 (j : Fin 15) : Fin 21 :=
  15

def coreSelector92_2 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 13 then
    15
  else
    14

def coreSelector92_3 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 11 then
    15
  else
    14

def coreSelector92_4 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 9 then
    15
  else
    if j.val ≤ 13 then
      14
    else
      13

def coreSelector92_5 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      15
    else
      14
  else
    if j.val ≤ 13 then
      13
    else
      16

def coreSelector92_6 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      15
    else
      14
  else
    if j.val ≤ 12 then
      13
    else
      16

def coreSelector92_7 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      15
    else
      14
  else
    if j.val ≤ 11 then
      13
    else
      16

def coreSelector92_8 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      15
    else
      14
  else
    if j.val ≤ 10 then
      13
    else
      if j.val ≤ 13 then
        16
      else
        12

def coreSelector92_9 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      14
    else
      13
  else
    if j.val ≤ 11 then
      16
    else
      if j.val ≤ 13 then
        12
      else
        20

def coreSelector92_10 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 8 then
    if j.val ≤ 1 then
      14
    else
      13
  else
    if j.val ≤ 9 then
      16
    else
      if j.val ≤ 12 then
        12
      else
        20

def coreSelector92_11 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 7 then
    13
  else
    if j.val ≤ 11 then
      12
    else
      20

def coreSelector92_12 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 10 then
    if j.val ≤ 5 then
      13
    else
      12
  else
    if j.val ≤ 12 then
      20
    else
      19

def coreSelector92_13 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 10 then
    if j.val ≤ 3 then
      13
    else
      if j.val ≤ 9 then
        12
      else
        11
  else
    if j.val ≤ 11 then
      19
    else
      if j.val ≤ 12 then
        10
      else
        18

def coreSelector92_14 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      13
    else
      if j.val ≤ 7 then
        12
      else
        11
  else
    if j.val ≤ 12 then
      if j.val ≤ 11 then
        10
      else
        18
    else
      if j.val ≤ 13 then
        17
      else
        9

def coreSelector92_15 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 10 then
    if j.val ≤ 5 then
      12
    else
      if j.val ≤ 7 then
        11
      else
        10
  else
    if j.val ≤ 11 then
      17
    else
      if j.val ≤ 13 then
        9
      else
        17

def coreSelector92_16 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      12
    else
      if j.val ≤ 5 then
        11
      else
        10
  else
    if j.val ≤ 12 then
      9
    else
      if j.val ≤ 13 then
        17
      else
        8

def coreSelector92_17 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      12
    else
      11
  else
    if j.val ≤ 7 then
      10
    else
      if j.val ≤ 11 then
        9
      else
        8

def coreSelector92_18 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
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

def coreSelector92_19 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      10
    else
      9
  else
    if j.val ≤ 11 then
      8
    else
      if j.val ≤ 13 then
        7
      else
        6

def coreSelector92_20 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      10
    else
      if j.val ≤ 5 then
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

def coreSelector92_21 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      9
    else
      if j.val ≤ 7 then
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

def coreSelector92_22 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      9
    else
      if j.val ≤ 5 then
        8
      else
        7
  else
    if j.val ≤ 11 then
      if j.val ≤ 9 then
        6
      else
        5
    else
      if j.val ≤ 13 then
        4
      else
        3

def coreSelector92_23 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
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
      if j.val ≤ 11 then
        4
      else
        3

def coreSelector92_24 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      8
    else
      if j.val ≤ 3 then
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

def coreSelector92_25 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      7
    else
      6
  else
    if j.val ≤ 5 then
      5
    else
      if j.val ≤ 7 then
        4
      else
        3

def coreSelector92_26 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      6
    else
      5
  else
    if j.val ≤ 5 then
      4
    else
      if j.val ≤ 13 then
        3
      else
        2

def coreSelector92_27 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      5
    else
      4
  else
    if j.val ≤ 11 then
      3
    else
      if j.val ≤ 13 then
        2
      else
        1

def coreSelector92_28 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 9 then
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

def coreSelector92_29 (j : Fin 15) : Fin 21 :=
  if j.val ≤ 9 then
    if j.val ≤ 7 then
      3
    else
      2
  else
    if j.val ≤ 12 then
      1
    else
      0

def coreSelector92_30 (j : Fin 15) : Fin 21 :=
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

def coreSelector92 (b : Fin 31) (j : Fin 15) : Fin 21 :=
  if b.val ≤ 14 then
    if b.val ≤ 6 then
      if b.val ≤ 2 then
        if b.val ≤ 0 then
          coreSelector92_0 j
        else
          if b.val ≤ 1 then
            coreSelector92_1 j
          else
            coreSelector92_2 j
      else
        if b.val ≤ 4 then
          if b.val ≤ 3 then
            coreSelector92_3 j
          else
            coreSelector92_4 j
        else
          if b.val ≤ 5 then
            coreSelector92_5 j
          else
            coreSelector92_6 j
    else
      if b.val ≤ 10 then
        if b.val ≤ 8 then
          if b.val ≤ 7 then
            coreSelector92_7 j
          else
            coreSelector92_8 j
        else
          if b.val ≤ 9 then
            coreSelector92_9 j
          else
            coreSelector92_10 j
      else
        if b.val ≤ 12 then
          if b.val ≤ 11 then
            coreSelector92_11 j
          else
            coreSelector92_12 j
        else
          if b.val ≤ 13 then
            coreSelector92_13 j
          else
            coreSelector92_14 j
  else
    if b.val ≤ 22 then
      if b.val ≤ 18 then
        if b.val ≤ 16 then
          if b.val ≤ 15 then
            coreSelector92_15 j
          else
            coreSelector92_16 j
        else
          if b.val ≤ 17 then
            coreSelector92_17 j
          else
            coreSelector92_18 j
      else
        if b.val ≤ 20 then
          if b.val ≤ 19 then
            coreSelector92_19 j
          else
            coreSelector92_20 j
        else
          if b.val ≤ 21 then
            coreSelector92_21 j
          else
            coreSelector92_22 j
    else
      if b.val ≤ 26 then
        if b.val ≤ 24 then
          if b.val ≤ 23 then
            coreSelector92_23 j
          else
            coreSelector92_24 j
        else
          if b.val ≤ 25 then
            coreSelector92_25 j
          else
            coreSelector92_26 j
      else
        if b.val ≤ 28 then
          if b.val ≤ 27 then
            coreSelector92_27 j
          else
            coreSelector92_28 j
        else
          if b.val ≤ 29 then
            coreSelector92_29 j
          else
            coreSelector92_30 j
def coreMetadataChunks92 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]
end Erdos883Verified
