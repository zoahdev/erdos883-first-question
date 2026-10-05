import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData114 : List CoreOddData :=
  [⟨1, [], [0, 0, 0, 0, 0]⟩,
   ⟨113, [113], [0, 0, 0, 0, 0]⟩,
   ⟨109, [109], [0, 0, 0, 0, 0]⟩,
   ⟨107, [107], [0, 0, 0, 0, 0]⟩,
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
   ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩,
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
   ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩,
   ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreResources114 (i : Fin 24) : CoreResourceData :=
  if i.val ≤ 11 then
    if i.val ≤ 5 then
      if i.val ≤ 2 then
        if i.val ≤ 0 then
          ⟨14, 0, 102, false⟩
        else
          if i.val ≤ 1 then
            ⟨16, 0, 52, true⟩
          else
            ⟨17, 0, 51, true⟩
      else
        if i.val ≤ 3 then
          ⟨22, 0, 50, true⟩
        else
          if i.val ≤ 4 then
            ⟨23, 0, 49, true⟩
          else
            ⟨24, 0, 48, true⟩
    else
      if i.val ≤ 8 then
        if i.val ≤ 6 then
          ⟨25, 0, 47, true⟩
        else
          if i.val ≤ 7 then
            ⟨26, 0, 45, true⟩
          else
            ⟨27, 0, 44, true⟩
      else
        if i.val ≤ 9 then
          ⟨29, 0, 41, true⟩
        else
          if i.val ≤ 10 then
            ⟨31, 0, 36, true⟩
          else
            ⟨33, 0, 32, true⟩
  else
    if i.val ≤ 17 then
      if i.val ≤ 14 then
        if i.val ≤ 12 then
          ⟨34, 0, 30, true⟩
        else
          if i.val ≤ 13 then
            ⟨35, 0, 29, true⟩
          else
            ⟨38, 0, 28, true⟩
      else
        if i.val ≤ 15 then
          ⟨42, 0, 24, true⟩
        else
          if i.val ≤ 16 then
            ⟨45, 0, 23, true⟩
          else
            ⟨48, 0, 22, true⟩
    else
      if i.val ≤ 20 then
        if i.val ≤ 18 then
          ⟨57, 0, 21, true⟩
        else
          if i.val ≤ 19 then
            ⟨45, 1, 28, true⟩
          else
            ⟨35, 2, 37, true⟩
      else
        if i.val ≤ 21 then
          ⟨36, 2, 35, true⟩
        else
          if i.val ≤ 22 then
            ⟨37, 2, 34, true⟩
          else
            ⟨41, 2, 32, true⟩

def coreChunks114_0 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩]

def coreChunks114_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩]

def coreChunks114_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨47, [47], [0, 0, 0, 0, 0]⟩]

def coreChunks114_3 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]

def coreChunks114_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks114_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩]

def coreChunks114_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks114_7 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩]

def coreChunks114_8 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩]

def coreChunks114_9 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩]

def coreChunks114_10 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks114_11 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩]

def coreChunks114_12 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨95, [5, 19], [0, 0, 1, 2, 4]⟩]

def coreChunks114_13 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks114_14 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks114_15 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks114_16 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩]

def coreChunks114_17 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩]

def coreChunks114_18 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreChunks114_19 (c : Fin 3) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩]
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩]

def coreChunks114_20 (c : Fin 3) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩]
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks114_21 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩]

def coreChunks114_22 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨55, [5, 11], [0, 0, 1, 2, 5]⟩]

def coreChunks114_23 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreSelector114_0 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 17 then
    18
  else
    17

def coreSelector114_1 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 15 then
    18
  else
    17

def coreSelector114_2 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 13 then
    18
  else
    17

def coreSelector114_3 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 11 then
    18
  else
    if j.val ≤ 17 then
      17
    else
      16

def coreSelector114_4 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 9 then
    18
  else
    if j.val ≤ 15 then
      17
    else
      16

def coreSelector114_5 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      18
    else
      17
  else
    if j.val ≤ 17 then
      16
    else
      19

def coreSelector114_6 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      18
    else
      17
  else
    if j.val ≤ 16 then
      16
    else
      19

def coreSelector114_7 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      18
    else
      17
  else
    if j.val ≤ 15 then
      16
    else
      if j.val ≤ 16 then
        15
      else
        19

def coreSelector114_8 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      18
    else
      17
  else
    if j.val ≤ 13 then
      16
    else
      if j.val ≤ 15 then
        15
      else
        19

def coreSelector114_9 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      17
    else
      16
  else
    if j.val ≤ 14 then
      15
    else
      19

def coreSelector114_10 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      17
    else
      16
  else
    if j.val ≤ 13 then
      15
    else
      if j.val ≤ 17 then
        19
      else
        23

def coreSelector114_11 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 12 then
    if j.val ≤ 1 then
      17
    else
      if j.val ≤ 7 then
        16
      else
        15
  else
    if j.val ≤ 15 then
      19
    else
      if j.val ≤ 16 then
        14
      else
        23

def coreSelector114_12 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      16
    else
      15
  else
    if j.val ≤ 13 then
      19
    else
      if j.val ≤ 15 then
        14
      else
        23

def coreSelector114_13 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 10 then
    if j.val ≤ 3 then
      16
    else
      15
  else
    if j.val ≤ 11 then
      19
    else
      if j.val ≤ 14 then
        14
      else
        23

def coreSelector114_14 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      16
    else
      15
  else
    if j.val ≤ 13 then
      14
    else
      if j.val ≤ 16 then
        23
      else
        22

def coreSelector114_15 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 12 then
    if j.val ≤ 7 then
      15
    else
      14
  else
    if j.val ≤ 14 then
      23
    else
      if j.val ≤ 16 then
        22
      else
        21

def coreSelector114_16 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 12 then
    if j.val ≤ 5 then
      15
    else
      if j.val ≤ 11 then
        14
      else
        13
  else
    if j.val ≤ 14 then
      22
    else
      if j.val ≤ 16 then
        21
      else
        20

def coreSelector114_17 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 12 then
    if j.val ≤ 9 then
      if j.val ≤ 3 then
        15
      else
        14
    else
      if j.val ≤ 11 then
        13
      else
        12
  else
    if j.val ≤ 14 then
      if j.val ≤ 13 then
        21
      else
        11
    else
      if j.val ≤ 17 then
        20
      else
        10

def coreSelector114_18 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      if j.val ≤ 1 then
        15
      else
        14
    else
      if j.val ≤ 9 then
        13
      else
        12
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        11
      else
        20
    else
      if j.val ≤ 17 then
        10
      else
        20

def coreSelector114_19 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 12 then
    if j.val ≤ 7 then
      if j.val ≤ 5 then
        14
      else
        13
    else
      if j.val ≤ 9 then
        12
      else
        11
  else
    if j.val ≤ 16 then
      if j.val ≤ 13 then
        20
      else
        10
    else
      if j.val ≤ 17 then
        20
      else
        9

def coreSelector114_20 (j : Fin 19) : Fin 24 :=
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

def coreSelector114_21 (j : Fin 19) : Fin 24 :=
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
      if j.val ≤ 17 then
        9
      else
        8

def coreSelector114_22 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      13
    else
      if j.val ≤ 3 then
        12
      else
        11
  else
    if j.val ≤ 15 then
      if j.val ≤ 11 then
        10
      else
        9
    else
      if j.val ≤ 17 then
        8
      else
        7

def coreSelector114_23 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      12
    else
      if j.val ≤ 5 then
        11
      else
        10
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        9
      else
        8
    else
      if j.val ≤ 17 then
        7
      else
        6

def coreSelector114_24 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      11
    else
      if j.val ≤ 7 then
        10
      else
        9
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        8
      else
        7
    else
      if j.val ≤ 17 then
        6
      else
        5

def coreSelector114_25 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        11
      else
        10
    else
      if j.val ≤ 9 then
        9
      else
        8
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        7
      else
        6
    else
      if j.val ≤ 17 then
        5
      else
        4

def coreSelector114_26 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        10
      else
        9
    else
      if j.val ≤ 9 then
        8
      else
        7
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        6
      else
        5
    else
      if j.val ≤ 17 then
        4
      else
        3

def coreSelector114_27 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        10
      else
        9
    else
      if j.val ≤ 7 then
        8
      else
        7
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        6
      else
        5
    else
      if j.val ≤ 15 then
        4
      else
        3

def coreSelector114_28 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
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

def coreSelector114_29 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      9
    else
      if j.val ≤ 3 then
        8
      else
        7
  else
    if j.val ≤ 9 then
      if j.val ≤ 7 then
        6
      else
        5
    else
      if j.val ≤ 11 then
        4
      else
        3

def coreSelector114_30 (j : Fin 19) : Fin 24 :=
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

def coreSelector114_31 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      7
    else
      if j.val ≤ 3 then
        6
      else
        5
  else
    if j.val ≤ 7 then
      4
    else
      if j.val ≤ 17 then
        3
      else
        2

def coreSelector114_32 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      6
    else
      if j.val ≤ 3 then
        5
      else
        4
  else
    if j.val ≤ 15 then
      3
    else
      if j.val ≤ 17 then
        2
      else
        1

def coreSelector114_33 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 3 then
    if j.val ≤ 1 then
      5
    else
      4
  else
    if j.val ≤ 13 then
      3
    else
      if j.val ≤ 15 then
        2
      else
        1

def coreSelector114_34 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 1 then
      4
    else
      3
  else
    if j.val ≤ 13 then
      2
    else
      if j.val ≤ 17 then
        1
      else
        0

def coreSelector114_35 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 11 then
    if j.val ≤ 9 then
      3
    else
      2
  else
    if j.val ≤ 16 then
      1
    else
      0

def coreSelector114_36 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 9 then
    if j.val ≤ 7 then
      3
    else
      2
  else
    if j.val ≤ 15 then
      1
    else
      0

def coreSelector114_37 (j : Fin 19) : Fin 24 :=
  if j.val ≤ 7 then
    if j.val ≤ 5 then
      3
    else
      2
  else
    if j.val ≤ 14 then
      1
    else
      0

def coreSelector114 (b : Fin 38) (j : Fin 19) : Fin 24 :=
  if b.val ≤ 18 then
    if b.val ≤ 8 then
      if b.val ≤ 3 then
        if b.val ≤ 1 then
          if b.val ≤ 0 then
            coreSelector114_0 j
          else
            coreSelector114_1 j
        else
          if b.val ≤ 2 then
            coreSelector114_2 j
          else
            coreSelector114_3 j
      else
        if b.val ≤ 5 then
          if b.val ≤ 4 then
            coreSelector114_4 j
          else
            coreSelector114_5 j
        else
          if b.val ≤ 6 then
            coreSelector114_6 j
          else
            if b.val ≤ 7 then
              coreSelector114_7 j
            else
              coreSelector114_8 j
    else
      if b.val ≤ 13 then
        if b.val ≤ 10 then
          if b.val ≤ 9 then
            coreSelector114_9 j
          else
            coreSelector114_10 j
        else
          if b.val ≤ 11 then
            coreSelector114_11 j
          else
            if b.val ≤ 12 then
              coreSelector114_12 j
            else
              coreSelector114_13 j
      else
        if b.val ≤ 15 then
          if b.val ≤ 14 then
            coreSelector114_14 j
          else
            coreSelector114_15 j
        else
          if b.val ≤ 16 then
            coreSelector114_16 j
          else
            if b.val ≤ 17 then
              coreSelector114_17 j
            else
              coreSelector114_18 j
  else
    if b.val ≤ 27 then
      if b.val ≤ 22 then
        if b.val ≤ 20 then
          if b.val ≤ 19 then
            coreSelector114_19 j
          else
            coreSelector114_20 j
        else
          if b.val ≤ 21 then
            coreSelector114_21 j
          else
            coreSelector114_22 j
      else
        if b.val ≤ 24 then
          if b.val ≤ 23 then
            coreSelector114_23 j
          else
            coreSelector114_24 j
        else
          if b.val ≤ 25 then
            coreSelector114_25 j
          else
            if b.val ≤ 26 then
              coreSelector114_26 j
            else
              coreSelector114_27 j
    else
      if b.val ≤ 32 then
        if b.val ≤ 29 then
          if b.val ≤ 28 then
            coreSelector114_28 j
          else
            coreSelector114_29 j
        else
          if b.val ≤ 30 then
            coreSelector114_30 j
          else
            if b.val ≤ 31 then
              coreSelector114_31 j
            else
              coreSelector114_32 j
      else
        if b.val ≤ 34 then
          if b.val ≤ 33 then
            coreSelector114_33 j
          else
            coreSelector114_34 j
        else
          if b.val ≤ 35 then
            coreSelector114_35 j
          else
            if b.val ≤ 36 then
              coreSelector114_36 j
            else
              coreSelector114_37 j
def coreMetadataChunks114 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]
end Erdos883Verified
