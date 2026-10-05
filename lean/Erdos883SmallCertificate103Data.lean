import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData103 : List CoreOddData :=
  [⟨1, [], [0, 0, 0, 0, 0]⟩,
   ⟨103, [103], [0, 0, 0, 0, 0]⟩,
   ⟨101, [101], [0, 0, 0, 0, 0]⟩,
   ⟨97, [97], [0, 0, 0, 0, 0]⟩,
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
   ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩,
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
   ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩,
   ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]

def coreResources103 (i : Fin 25) : CoreResourceData :=
  if i.val ≤ 11 then
    if i.val ≤ 5 then
      if i.val ≤ 2 then
        if i.val ≤ 0 then
          ⟨13, 0, 92, false⟩
        else
          if i.val ≤ 1 then
            ⟨14, 0, 91, false⟩
          else
            ⟨15, 0, 90, false⟩
      else
        if i.val ≤ 3 then
          ⟨13, 0, 47, true⟩
        else
          if i.val ≤ 4 then
            ⟨14, 0, 46, true⟩
          else
            ⟨19, 0, 45, true⟩
    else
      if i.val ≤ 8 then
        if i.val ≤ 6 then
          ⟨20, 0, 44, true⟩
        else
          if i.val ≤ 7 then
            ⟨22, 0, 43, true⟩
          else
            ⟨23, 0, 42, true⟩
      else
        if i.val ≤ 9 then
          ⟨24, 0, 40, true⟩
        else
          if i.val ≤ 10 then
            ⟨26, 0, 37, true⟩
          else
            ⟨28, 0, 33, true⟩
  else
    if i.val ≤ 17 then
      if i.val ≤ 14 then
        if i.val ≤ 12 then
          ⟨29, 0, 30, true⟩
        else
          if i.val ≤ 13 then
            ⟨30, 0, 29, true⟩
          else
            ⟨32, 0, 27, true⟩
      else
        if i.val ≤ 15 then
          ⟨35, 0, 26, true⟩
        else
          if i.val ≤ 16 then
            ⟨39, 0, 23, true⟩
          else
            ⟨41, 0, 22, true⟩
    else
      if i.val ≤ 20 then
        if i.val ≤ 18 then
          ⟨45, 0, 21, true⟩
        else
          if i.val ≤ 19 then
            ⟨52, 0, 20, true⟩
          else
            ⟨39, 1, 26, true⟩
      else
        if i.val ≤ 22 then
          if i.val ≤ 21 then
            ⟨32, 2, 34, true⟩
          else
            ⟨33, 2, 33, true⟩
        else
          if i.val ≤ 23 then
            ⟨34, 2, 31, true⟩
          else
            ⟨37, 2, 29, true⟩

def coreChunks103_0 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩]

def coreChunks103_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨47, [47], [0, 0, 0, 0, 0]⟩]

def coreChunks103_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨43, [43], [0, 0, 0, 0, 0]⟩]

def coreChunks103_3 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩]

def coreChunks103_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨47, [47], [0, 0, 0, 0, 0]⟩]

def coreChunks103_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]

def coreChunks103_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks103_7 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks103_8 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩]

def coreChunks103_9 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩]

def coreChunks103_10 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩]

def coreChunks103_11 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks103_12 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩]

def coreChunks103_13 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩]

def coreChunks103_14 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks103_15 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks103_16 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks103_17 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩]

def coreChunks103_18 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩]

def coreChunks103_19 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]

def coreChunks103_20 (c : Fin 3) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks103_21 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks103_22 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩]

def coreChunks103_23 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨55, [5, 11], [0, 0, 1, 2, 5]⟩]

def coreChunks103_24 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩]

def coreSelector103_0 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 13 then
    19
  else
    18

def coreSelector103_1 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 11 then
    19
  else
    18

def coreSelector103_2 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 9 then
    19
  else
    18

def coreSelector103_3 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 7 then
    19
  else
    if j.val ≤ 15 then
      18
    else
      17

def coreSelector103_4 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 5 then
    19
  else
    if j.val ≤ 13 then
      18
    else
      17

def coreSelector103_5 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      19
    else
      18
  else
    if j.val ≤ 15 then
      17
    else
      16

def coreSelector103_6 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      19
    else
      18
  else
    if j.val ≤ 13 then
      17
    else
      16

def coreSelector103_7 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      18
    else
      17
  else
    if j.val ≤ 15 then
      16
    else
      20

def coreSelector103_8 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      18
    else
      17
  else
    if j.val ≤ 14 then
      16
    else
      20

def coreSelector103_9 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      18
    else
      17
  else
    if j.val ≤ 13 then
      16
    else
      if j.val ≤ 15 then
        20
      else
        15

def coreSelector103_10 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 12 then
    if j.val ≤ 1 then
      18
    else
      if j.val ≤ 5 then
        17
      else
        16
  else
    if j.val ≤ 13 then
      20
    else
      if j.val ≤ 15 then
        15
      else
        24

def coreSelector103_11 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      17
    else
      16
  else
    if j.val ≤ 14 then
      15
    else
      24

def coreSelector103_12 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      17
    else
      16
  else
    if j.val ≤ 13 then
      15
    else
      24

def coreSelector103_13 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 12 then
    if j.val ≤ 7 then
      16
    else
      15
  else
    if j.val ≤ 14 then
      24
    else
      23

def coreSelector103_14 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      16
    else
      15
  else
    if j.val ≤ 12 then
      14
    else
      if j.val ≤ 14 then
        23
      else
        22

def coreSelector103_15 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      16
    else
      if j.val ≤ 9 then
        15
      else
        14
  else
    if j.val ≤ 12 then
      23
    else
      if j.val ≤ 14 then
        22
      else
        21

def coreSelector103_16 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 10 then
    if j.val ≤ 1 then
      16
    else
      if j.val ≤ 7 then
        15
      else
        14
  else
    if j.val ≤ 12 then
      if j.val ≤ 11 then
        22
      else
        13
    else
      if j.val ≤ 15 then
        21
      else
        11

def coreSelector103_17 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      15
    else
      if j.val ≤ 9 then
        14
      else
        13
  else
    if j.val ≤ 13 then
      if j.val ≤ 12 then
        12
      else
        21
    else
      if j.val ≤ 15 then
        11
      else
        21

def coreSelector103_18 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      15
    else
      if j.val ≤ 7 then
        14
      else
        13
  else
    if j.val ≤ 14 then
      if j.val ≤ 11 then
        12
      else
        11
    else
      if j.val ≤ 15 then
        21
      else
        10

def coreSelector103_19 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      15
    else
      if j.val ≤ 5 then
        14
      else
        13
  else
    if j.val ≤ 9 then
      12
    else
      if j.val ≤ 13 then
        11
      else
        10

def coreSelector103_20 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      14
    else
      if j.val ≤ 5 then
        13
      else
        12
  else
    if j.val ≤ 11 then
      11
    else
      if j.val ≤ 15 then
        10
      else
        9

def coreSelector103_21 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      14
    else
      if j.val ≤ 3 then
        13
      else
        12
  else
    if j.val ≤ 13 then
      if j.val ≤ 9 then
        11
      else
        10
    else
      if j.val ≤ 15 then
        9
      else
        8

def coreSelector103_22 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      13
    else
      if j.val ≤ 3 then
        12
      else
        11
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        10
      else
        9
    else
      if j.val ≤ 15 then
        8
      else
        7

def coreSelector103_23 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      12
    else
      if j.val ≤ 5 then
        11
      else
        10
  else
    if j.val ≤ 11 then
      9
    else
      if j.val ≤ 13 then
        8
      else
        7

def coreSelector103_24 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      11
    else
      if j.val ≤ 7 then
        10
      else
        9
  else
    if j.val ≤ 11 then
      8
    else
      if j.val ≤ 15 then
        7
      else
        6

def coreSelector103_25 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      11
    else
      if j.val ≤ 5 then
        10
      else
        9
  else
    if j.val ≤ 13 then
      if j.val ≤ 9 then
        8
      else
        7
    else
      if j.val ≤ 15 then
        6
      else
        5

def coreSelector103_26 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
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

def coreSelector103_27 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      10
    else
      if j.val ≤ 3 then
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

def coreSelector103_28 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      9
    else
      8
  else
    if j.val ≤ 7 then
      7
    else
      if j.val ≤ 9 then
        6
      else
        5

def coreSelector103_29 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      8
    else
      7
  else
    if j.val ≤ 7 then
      6
    else
      if j.val ≤ 15 then
        5
      else
        2

def coreSelector103_30 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 5 then
    if j.val ≤ 3 then
      7
    else
      6
  else
    if j.val ≤ 14 then
      5
    else
      if j.val ≤ 15 then
        2
      else
        1

def coreSelector103_31 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 13 then
    if j.val ≤ 1 then
      7
    else
      if j.val ≤ 3 then
        6
      else
        5
  else
    if j.val ≤ 14 then
      4
    else
      if j.val ≤ 15 then
        1
      else
        0

def coreSelector103_32 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 11 then
    if j.val ≤ 1 then
      6
    else
      5
  else
    if j.val ≤ 13 then
      4
    else
      if j.val ≤ 14 then
        3
      else
        0

def coreSelector103_33 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 11 then
    if j.val ≤ 9 then
      5
    else
      4
  else
    if j.val ≤ 13 then
      3
    else
      0

def coreSelector103_34 (j : Fin 17) : Fin 25 :=
  if j.val ≤ 9 then
    if j.val ≤ 7 then
      5
    else
      4
  else
    if j.val ≤ 12 then
      3
    else
      0

def coreSelector103 (b : Fin 35) (j : Fin 17) : Fin 25 :=
  if b.val ≤ 16 then
    if b.val ≤ 7 then
      if b.val ≤ 3 then
        if b.val ≤ 1 then
          if b.val ≤ 0 then
            coreSelector103_0 j
          else
            coreSelector103_1 j
        else
          if b.val ≤ 2 then
            coreSelector103_2 j
          else
            coreSelector103_3 j
      else
        if b.val ≤ 5 then
          if b.val ≤ 4 then
            coreSelector103_4 j
          else
            coreSelector103_5 j
        else
          if b.val ≤ 6 then
            coreSelector103_6 j
          else
            coreSelector103_7 j
    else
      if b.val ≤ 11 then
        if b.val ≤ 9 then
          if b.val ≤ 8 then
            coreSelector103_8 j
          else
            coreSelector103_9 j
        else
          if b.val ≤ 10 then
            coreSelector103_10 j
          else
            coreSelector103_11 j
      else
        if b.val ≤ 13 then
          if b.val ≤ 12 then
            coreSelector103_12 j
          else
            coreSelector103_13 j
        else
          if b.val ≤ 14 then
            coreSelector103_14 j
          else
            if b.val ≤ 15 then
              coreSelector103_15 j
            else
              coreSelector103_16 j
  else
    if b.val ≤ 25 then
      if b.val ≤ 20 then
        if b.val ≤ 18 then
          if b.val ≤ 17 then
            coreSelector103_17 j
          else
            coreSelector103_18 j
        else
          if b.val ≤ 19 then
            coreSelector103_19 j
          else
            coreSelector103_20 j
      else
        if b.val ≤ 22 then
          if b.val ≤ 21 then
            coreSelector103_21 j
          else
            coreSelector103_22 j
        else
          if b.val ≤ 23 then
            coreSelector103_23 j
          else
            if b.val ≤ 24 then
              coreSelector103_24 j
            else
              coreSelector103_25 j
    else
      if b.val ≤ 29 then
        if b.val ≤ 27 then
          if b.val ≤ 26 then
            coreSelector103_26 j
          else
            coreSelector103_27 j
        else
          if b.val ≤ 28 then
            coreSelector103_28 j
          else
            coreSelector103_29 j
      else
        if b.val ≤ 31 then
          if b.val ≤ 30 then
            coreSelector103_30 j
          else
            coreSelector103_31 j
        else
          if b.val ≤ 32 then
            coreSelector103_32 j
          else
            if b.val ≤ 33 then
              coreSelector103_33 j
            else
              coreSelector103_34 j
def coreMetadataChunks103 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]
end Erdos883Verified
