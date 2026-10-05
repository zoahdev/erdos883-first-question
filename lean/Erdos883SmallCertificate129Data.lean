import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData129 : List CoreOddData :=
  [⟨1, [], [0, 0, 0, 0, 0]⟩,
   ⟨127, [127], [0, 0, 0, 0, 0]⟩,
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
   ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩,
   ⟨7, [7], [0, 0, 0, 1, 2]⟩,
   ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩,
   ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩,
   ⟨5, [5], [0, 0, 1, 2, 4]⟩,
   ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩,
   ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩,
   ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩,
   ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩,
   ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩,
   ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩,
   ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩,
   ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩,
   ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩,
   ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩,
   ⟨3, [3], [0, 1, 2, 4, 8]⟩,
   ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩,
   ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩,
   ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩,
   ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩,
   ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩,
   ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩,
   ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩,
   ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩,
   ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩,
   ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩,
   ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩,
   ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩,
   ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩,
   ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreResources129 (i : Fin 32) : CoreResourceData :=
  if i.val ≤ 15 then
    if i.val ≤ 7 then
      if i.val ≤ 3 then
        if i.val ≤ 1 then
          if i.val ≤ 0 then
            ⟨15, 0, 116, false⟩
          else
            ⟨16, 0, 115, false⟩
        else
          if i.val ≤ 2 then
            ⟨18, 0, 114, false⟩
          else
            ⟨32, 0, 87, false⟩
      else
        if i.val ≤ 5 then
          if i.val ≤ 4 then
            ⟨33, 0, 77, false⟩
          else
            ⟨15, 0, 59, true⟩
        else
          if i.val ≤ 6 then
            ⟨16, 0, 58, true⟩
          else
            ⟨22, 0, 57, true⟩
    else
      if i.val ≤ 11 then
        if i.val ≤ 9 then
          if i.val ≤ 8 then
            ⟨23, 0, 56, true⟩
          else
            ⟨24, 0, 55, true⟩
        else
          if i.val ≤ 10 then
            ⟨25, 0, 54, true⟩
          else
            ⟨26, 0, 53, true⟩
      else
        if i.val ≤ 13 then
          if i.val ≤ 12 then
            ⟨27, 0, 52, true⟩
          else
            ⟨29, 0, 50, true⟩
        else
          if i.val ≤ 14 then
            ⟨31, 0, 46, true⟩
          else
            ⟨32, 0, 43, true⟩
  else
    if i.val ≤ 23 then
      if i.val ≤ 19 then
        if i.val ≤ 17 then
          if i.val ≤ 16 then
            ⟨35, 0, 38, true⟩
          else
            ⟨37, 0, 37, true⟩
        else
          if i.val ≤ 18 then
            ⟨38, 0, 35, true⟩
          else
            ⟨40, 0, 34, true⟩
      else
        if i.val ≤ 21 then
          if i.val ≤ 20 then
            ⟨43, 0, 33, true⟩
          else
            ⟨47, 0, 27, true⟩
        else
          if i.val ≤ 22 then
            ⟨51, 0, 26, true⟩
          else
            ⟨55, 0, 25, true⟩
    else
      if i.val ≤ 27 then
        if i.val ≤ 25 then
          if i.val ≤ 24 then
            ⟨65, 0, 24, true⟩
          else
            ⟨51, 1, 33, true⟩
        else
          if i.val ≤ 26 then
            ⟨36, 2, 85, false⟩
          else
            ⟨35, 2, 43, true⟩
      else
        if i.val ≤ 29 then
          if i.val ≤ 28 then
            ⟨40, 2, 42, true⟩
          else
            ⟨41, 2, 41, true⟩
        else
          if i.val ≤ 30 then
            ⟨42, 2, 40, true⟩
          else
            ⟨45, 2, 37, true⟩

def coreChunks129_0 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩]

def coreChunks129_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨59, [59], [0, 0, 0, 0, 0]⟩]

def coreChunks129_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩]

def coreChunks129_3 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]

def coreChunks129_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩]

def coreChunks129_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩]

def coreChunks129_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨59, [59], [0, 0, 0, 0, 0]⟩]

def coreChunks129_7 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩]

def coreChunks129_8 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨29, [29], [0, 0, 0, 0, 0]⟩]

def coreChunks129_9 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks129_10 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩]

def coreChunks129_11 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks129_12 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩]

def coreChunks129_13 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩]

def coreChunks129_14 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩]

def coreChunks129_15 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]

def coreChunks129_16 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks129_17 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩]

def coreChunks129_18 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨115, [5, 23], [0, 0, 1, 2, 4]⟩]

def coreChunks129_19 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks129_20 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks129_21 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks129_22 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩]

def coreChunks129_23 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩]

def coreChunks129_24 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreChunks129_25 (c : Fin 4) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]
  | 2 => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩]
  | _ => [⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩]

def coreChunks129_26 (c : Fin 3) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩]

def coreChunks129_27 (c : Fin 3) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks129_28 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks129_29 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩]

def coreChunks129_30 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨55, [5, 11], [0, 0, 1, 2, 5]⟩]

def coreChunks129_31 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩]

def coreSelector129_0 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 19 then
    24
  else
    23

def coreSelector129_1 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 17 then
    24
  else
    23

def coreSelector129_2 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 15 then
    24
  else
    23

def coreSelector129_3 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 13 then
    24
  else
    23

def coreSelector129_4 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    24
  else
    if j.val ≤ 19 then
      23
    else
      22

def coreSelector129_5 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 9 then
    24
  else
    if j.val ≤ 17 then
      23
    else
      22

def coreSelector129_6 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      24
    else
      23
  else
    if j.val ≤ 19 then
      22
    else
      25

def coreSelector129_7 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      24
    else
      23
  else
    if j.val ≤ 18 then
      22
    else
      25

def coreSelector129_8 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      24
    else
      23
  else
    if j.val ≤ 17 then
      22
    else
      25

def coreSelector129_9 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      24
    else
      23
  else
    if j.val ≤ 16 then
      22
    else
      25

def coreSelector129_10 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      23
    else
      22
  else
    if j.val ≤ 16 then
      21
    else
      25

def coreSelector129_11 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      23
    else
      22
  else
    if j.val ≤ 15 then
      21
    else
      25

def coreSelector129_12 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      23
    else
      22
  else
    if j.val ≤ 14 then
      21
    else
      if j.val ≤ 19 then
        25
      else
        20

def coreSelector129_13 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 13 then
    if j.val ≤ 1 then
      23
    else
      if j.val ≤ 9 then
        22
      else
        21
  else
    if j.val ≤ 17 then
      25
    else
      if j.val ≤ 19 then
        20
      else
        31

def coreSelector129_14 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 12 then
    if j.val ≤ 7 then
      22
    else
      21
  else
    if j.val ≤ 15 then
      25
    else
      if j.val ≤ 18 then
        20
      else
        31

def coreSelector129_15 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      22
    else
      21
  else
    if j.val ≤ 13 then
      25
    else
      if j.val ≤ 17 then
        20
      else
        31

def coreSelector129_16 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      22
    else
      if j.val ≤ 10 then
        21
      else
        25
  else
    if j.val ≤ 16 then
      20
    else
      if j.val ≤ 18 then
        31
      else
        30

def coreSelector129_17 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 15 then
    if j.val ≤ 1 then
      22
    else
      if j.val ≤ 9 then
        21
      else
        20
  else
    if j.val ≤ 16 then
      19
    else
      if j.val ≤ 18 then
        30
      else
        29

def coreSelector129_18 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      21
    else
      if j.val ≤ 13 then
        20
      else
        19
  else
    if j.val ≤ 16 then
      30
    else
      if j.val ≤ 18 then
        29
      else
        28

def coreSelector129_19 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      21
    else
      20
  else
    if j.val ≤ 14 then
      19
    else
      if j.val ≤ 16 then
        29
      else
        28

def coreSelector129_20 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      21
    else
      if j.val ≤ 9 then
        20
      else
        19
  else
    if j.val ≤ 15 then
      if j.val ≤ 14 then
        18
      else
        28
    else
      if j.val ≤ 16 then
        17
      else
        28

def coreSelector129_21 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 1 then
      21
    else
      if j.val ≤ 7 then
        20
      else
        19
  else
    if j.val ≤ 13 then
      18
    else
      if j.val ≤ 15 then
        17
      else
        28

def coreSelector129_22 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      20
    else
      if j.val ≤ 9 then
        19
      else
        18
  else
    if j.val ≤ 14 then
      17
    else
      if j.val ≤ 19 then
        28
      else
        26

def coreSelector129_23 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        20
      else
        19
    else
      if j.val ≤ 9 then
        18
      else
        17
  else
    if j.val ≤ 18 then
      if j.val ≤ 14 then
        16
      else
        28
    else
      if j.val ≤ 19 then
        27
      else
        3

def coreSelector129_24 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        20
      else
        19
    else
      if j.val ≤ 7 then
        18
      else
        if j.val ≤ 11 then
          17
        else
          16
  else
    if j.val ≤ 17 then
      if j.val ≤ 16 then
        28
      else
        27
    else
      if j.val ≤ 18 then
        15
      else
        if j.val ≤ 19 then
          3
        else
          14

def coreSelector129_25 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 12 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        19
      else
        18
    else
      if j.val ≤ 9 then
        17
      else
        16
  else
    if j.val ≤ 15 then
      if j.val ≤ 14 then
        28
      else
        27
    else
      if j.val ≤ 17 then
        15
      else
        14

def coreSelector129_26 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        19
      else
        18
    else
      if j.val ≤ 7 then
        17
      else
        16
  else
    if j.val ≤ 13 then
      if j.val ≤ 12 then
        4
      else
        27
    else
      if j.val ≤ 15 then
        15
      else
        if j.val ≤ 19 then
          14
        else
          13

def coreSelector129_27 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 10 then
    if j.val ≤ 1 then
      18
    else
      if j.val ≤ 5 then
        17
      else
        16
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        4
      else
        15
    else
      if j.val ≤ 17 then
        14
      else
        13

def coreSelector129_28 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      17
    else
      if j.val ≤ 9 then
        16
      else
        15
  else
    if j.val ≤ 15 then
      14
    else
      if j.val ≤ 19 then
        13
      else
        12

def coreSelector129_29 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      17
    else
      if j.val ≤ 7 then
        16
      else
        15
  else
    if j.val ≤ 17 then
      if j.val ≤ 13 then
        14
      else
        13
    else
      if j.val ≤ 19 then
        12
      else
        11

def coreSelector129_30 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      16
    else
      if j.val ≤ 7 then
        15
      else
        14
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        13
      else
        12
    else
      if j.val ≤ 19 then
        11
      else
        10

def coreSelector129_31 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        16
      else
        15
    else
      if j.val ≤ 9 then
        14
      else
        13
  else
    if j.val ≤ 17 then
      if j.val ≤ 15 then
        12
      else
        11
    else
      if j.val ≤ 19 then
        10
      else
        9

def coreSelector129_32 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        16
      else
        15
    else
      if j.val ≤ 7 then
        14
      else
        13
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        12
      else
        11
    else
      if j.val ≤ 17 then
        10
      else
        if j.val ≤ 19 then
          9
        else
          8

def coreSelector129_33 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
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
        10
    else
      if j.val ≤ 17 then
        9
      else
        if j.val ≤ 19 then
          8
        else
          7

def coreSelector129_34 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        14
      else
        13
    else
      if j.val ≤ 9 then
        12
      else
        11
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        10
      else
        9
    else
      if j.val ≤ 17 then
        8
      else
        7

def coreSelector129_35 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        14
      else
        13
    else
      if j.val ≤ 7 then
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

def coreSelector129_36 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      13
    else
      if j.val ≤ 5 then
        12
      else
        11
  else
    if j.val ≤ 11 then
      if j.val ≤ 9 then
        10
      else
        9
    else
      if j.val ≤ 13 then
        8
      else
        7

def coreSelector129_37 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        13
      else
        12
    else
      if j.val ≤ 5 then
        11
      else
        10
  else
    if j.val ≤ 11 then
      if j.val ≤ 9 then
        9
      else
        8
    else
      if j.val ≤ 19 then
        7
      else
        2

def coreSelector129_38 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      12
    else
      if j.val ≤ 3 then
        11
      else
        10
  else
    if j.val ≤ 9 then
      if j.val ≤ 7 then
        9
      else
        8
    else
      if j.val ≤ 18 then
        7
      else
        2

def coreSelector129_39 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      11
    else
      if j.val ≤ 3 then
        10
      else
        9
  else
    if j.val ≤ 17 then
      if j.val ≤ 7 then
        8
      else
        7
    else
      if j.val ≤ 19 then
        2
      else
        1

def coreSelector129_40 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      10
    else
      if j.val ≤ 3 then
        9
      else
        8
  else
    if j.val ≤ 17 then
      if j.val ≤ 16 then
        7
      else
        2
    else
      if j.val ≤ 19 then
        1
      else
        0

def coreSelector129_41 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 15 then
    if j.val ≤ 1 then
      9
    else
      if j.val ≤ 3 then
        8
      else
        7
  else
    if j.val ≤ 16 then
      6
    else
      if j.val ≤ 17 then
        1
      else
        0

def coreSelector129_42 (j : Fin 21) : Fin 32 :=
  if j.val ≤ 13 then
    if j.val ≤ 1 then
      8
    else
      7
  else
    if j.val ≤ 15 then
      6
    else
      if j.val ≤ 16 then
        5
      else
        0

def coreSelector129 (b : Fin 43) (j : Fin 21) : Fin 32 :=
  if b.val ≤ 20 then
    if b.val ≤ 9 then
      if b.val ≤ 4 then
        if b.val ≤ 1 then
          if b.val ≤ 0 then
            coreSelector129_0 j
          else
            coreSelector129_1 j
        else
          if b.val ≤ 2 then
            coreSelector129_2 j
          else
            if b.val ≤ 3 then
              coreSelector129_3 j
            else
              coreSelector129_4 j
      else
        if b.val ≤ 6 then
          if b.val ≤ 5 then
            coreSelector129_5 j
          else
            coreSelector129_6 j
        else
          if b.val ≤ 7 then
            coreSelector129_7 j
          else
            if b.val ≤ 8 then
              coreSelector129_8 j
            else
              coreSelector129_9 j
    else
      if b.val ≤ 14 then
        if b.val ≤ 11 then
          if b.val ≤ 10 then
            coreSelector129_10 j
          else
            coreSelector129_11 j
        else
          if b.val ≤ 12 then
            coreSelector129_12 j
          else
            if b.val ≤ 13 then
              coreSelector129_13 j
            else
              coreSelector129_14 j
      else
        if b.val ≤ 17 then
          if b.val ≤ 15 then
            coreSelector129_15 j
          else
            if b.val ≤ 16 then
              coreSelector129_16 j
            else
              coreSelector129_17 j
        else
          if b.val ≤ 18 then
            coreSelector129_18 j
          else
            if b.val ≤ 19 then
              coreSelector129_19 j
            else
              coreSelector129_20 j
  else
    if b.val ≤ 31 then
      if b.val ≤ 25 then
        if b.val ≤ 22 then
          if b.val ≤ 21 then
            coreSelector129_21 j
          else
            coreSelector129_22 j
        else
          if b.val ≤ 23 then
            coreSelector129_23 j
          else
            if b.val ≤ 24 then
              coreSelector129_24 j
            else
              coreSelector129_25 j
      else
        if b.val ≤ 28 then
          if b.val ≤ 26 then
            coreSelector129_26 j
          else
            if b.val ≤ 27 then
              coreSelector129_27 j
            else
              coreSelector129_28 j
        else
          if b.val ≤ 29 then
            coreSelector129_29 j
          else
            if b.val ≤ 30 then
              coreSelector129_30 j
            else
              coreSelector129_31 j
    else
      if b.val ≤ 36 then
        if b.val ≤ 33 then
          if b.val ≤ 32 then
            coreSelector129_32 j
          else
            coreSelector129_33 j
        else
          if b.val ≤ 34 then
            coreSelector129_34 j
          else
            if b.val ≤ 35 then
              coreSelector129_35 j
            else
              coreSelector129_36 j
      else
        if b.val ≤ 39 then
          if b.val ≤ 37 then
            coreSelector129_37 j
          else
            if b.val ≤ 38 then
              coreSelector129_38 j
            else
              coreSelector129_39 j
        else
          if b.val ≤ 40 then
            coreSelector129_40 j
          else
            if b.val ≤ 41 then
              coreSelector129_41 j
            else
              coreSelector129_42 j
def coreMetadataChunks129 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩]
  | _ => [⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]
end Erdos883Verified
