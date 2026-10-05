import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData158 : List CoreOddData :=
  [⟨1, [], [0, 0, 0, 0, 0]⟩,
   ⟨157, [157], [0, 0, 0, 0, 0]⟩,
   ⟨151, [151], [0, 0, 0, 0, 0]⟩,
   ⟨149, [149], [0, 0, 0, 0, 0]⟩,
   ⟨139, [139], [0, 0, 0, 0, 0]⟩,
   ⟨137, [137], [0, 0, 0, 0, 0]⟩,
   ⟨131, [131], [0, 0, 0, 0, 0]⟩,
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
   ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩,
   ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩,
   ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩,
   ⟨5, [5], [0, 0, 1, 2, 4]⟩,
   ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩,
   ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩,
   ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩,
   ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩,
   ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩,
   ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩,
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
   ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩,
   ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩,
   ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩,
   ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩,
   ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩,
   ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩,
   ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩,
   ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩,
   ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩,
   ⟨153, [3, 3, 17], [0, 1, 2, 4, 8]⟩,
   ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩,
   ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩,
   ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩,
   ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩,
   ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨147, [3, 7, 7], [0, 1, 2, 5, 10]⟩,
   ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩,
   ⟨135, [3, 3, 3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreResources158 (i : Fin 38) : CoreResourceData :=
  if i.val ≤ 18 then
    if i.val ≤ 8 then
      if i.val ≤ 3 then
        if i.val ≤ 1 then
          if i.val ≤ 0 then
            ⟨18, 0, 142, false⟩
          else
            ⟨19, 0, 141, false⟩
        else
          if i.val ≤ 2 then
            ⟨22, 0, 140, false⟩
          else
            ⟨36, 0, 112, false⟩
      else
        if i.val ≤ 5 then
          if i.val ≤ 4 then
            ⟨38, 0, 103, false⟩
          else
            ⟨39, 0, 97, false⟩
        else
          if i.val ≤ 6 then
            ⟨40, 0, 96, false⟩
          else
            if i.val ≤ 7 then
              ⟨18, 0, 72, true⟩
            else
              ⟨19, 0, 71, true⟩
    else
      if i.val ≤ 13 then
        if i.val ≤ 10 then
          if i.val ≤ 9 then
            ⟨27, 0, 70, true⟩
          else
            ⟨28, 0, 69, true⟩
        else
          if i.val ≤ 11 then
            ⟨29, 0, 68, true⟩
          else
            if i.val ≤ 12 then
              ⟨30, 0, 67, true⟩
            else
              ⟨31, 0, 66, true⟩
      else
        if i.val ≤ 15 then
          if i.val ≤ 14 then
            ⟨32, 0, 65, true⟩
          else
            ⟨33, 0, 63, true⟩
        else
          if i.val ≤ 16 then
            ⟨35, 0, 61, true⟩
          else
            if i.val ≤ 17 then
              ⟨37, 0, 56, true⟩
            else
              ⟨38, 0, 51, true⟩
  else
    if i.val ≤ 27 then
      if i.val ≤ 22 then
        if i.val ≤ 20 then
          if i.val ≤ 19 then
            ⟨39, 0, 48, true⟩
          else
            ⟨40, 0, 47, true⟩
        else
          if i.val ≤ 21 then
            ⟨44, 0, 46, true⟩
          else
            ⟨45, 0, 45, true⟩
      else
        if i.val ≤ 24 then
          if i.val ≤ 23 then
            ⟨47, 0, 43, true⟩
          else
            ⟨49, 0, 42, true⟩
        else
          if i.val ≤ 25 then
            ⟨53, 0, 41, true⟩
          else
            if i.val ≤ 26 then
              ⟨57, 0, 33, true⟩
            else
              ⟨61, 0, 32, true⟩
    else
      if i.val ≤ 32 then
        if i.val ≤ 29 then
          if i.val ≤ 28 then
            ⟨65, 0, 31, true⟩
          else
            ⟨78, 0, 30, true⟩
        else
          if i.val ≤ 30 then
            ⟨79, 0, 27, true⟩
          else
            if i.val ≤ 31 then
              ⟨61, 1, 41, true⟩
            else
              ⟨52, 2, 47, true⟩
      else
        if i.val ≤ 34 then
          if i.val ≤ 33 then
            ⟨53, 2, 45, true⟩
          else
            ⟨43, 3, 55, true⟩
        else
          if i.val ≤ 35 then
            ⟨44, 3, 53, true⟩
          else
            if i.val ≤ 36 then
              ⟨49, 3, 51, true⟩
            else
              ⟨49, 4, 52, true⟩

def coreChunks158_0 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩]

def coreChunks158_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨71, [71], [0, 0, 0, 0, 0]⟩]

def coreChunks158_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩]

def coreChunks158_3 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩]

def coreChunks158_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩]

def coreChunks158_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨133, [7, 19], [0, 0, 0, 1, 2]⟩]

def coreChunks158_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]

def coreChunks158_7 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩]

def coreChunks158_8 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨71, [71], [0, 0, 0, 0, 0]⟩]

def coreChunks158_9 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩]

def coreChunks158_10 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨31, [31], [0, 0, 0, 0, 0]⟩]

def coreChunks158_11 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨29, [29], [0, 0, 0, 0, 0]⟩]

def coreChunks158_12 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks158_13 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩]

def coreChunks158_14 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks158_15 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩]

def coreChunks158_16 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩]

def coreChunks158_17 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩]

def coreChunks158_18 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨143, [11, 13], [0, 0, 0, 0, 1]⟩]

def coreChunks158_19 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨133, [7, 19], [0, 0, 0, 1, 2]⟩]

def coreChunks158_20 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]

def coreChunks158_21 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩]

def coreChunks158_22 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩]

def coreChunks158_23 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩]

def coreChunks158_24 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩]

def coreChunks158_25 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks158_26 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks158_27 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨141, [3, 47], [0, 1, 2, 4, 8]⟩, ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩]

def coreChunks158_28 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩]

def coreChunks158_29 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨153, [3, 3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨147, [3, 7, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨135, [3, 3, 3, 5], [0, 1, 3, 6, 12]⟩]

def coreChunks158_30 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreChunks158_31 (c : Fin 4) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩]
  | _ => [⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩, ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩]

def coreChunks158_32 (c : Fin 4) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩]
  | _ => [⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩]

def coreChunks158_33 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨35, [5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks158_34 (c : Fin 3) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks158_35 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩]

def coreChunks158_36 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩]

def coreChunks158_37 (c : Fin 4) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩]
  | _ => [⟨95, [5, 19], [0, 0, 1, 2, 4]⟩]

def coreSelector158_0 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 1 then
    30
  else
    29

def coreSelector158_1 (j : Fin 26) : Fin 38 :=
  29

def coreSelector158_2 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 23 then
    29
  else
    28

def coreSelector158_3 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 21 then
    29
  else
    28

def coreSelector158_4 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 19 then
    29
  else
    28

def coreSelector158_5 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 17 then
    29
  else
    28

def coreSelector158_6 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 15 then
    29
  else
    if j.val ≤ 23 then
      28
    else
      27

def coreSelector158_7 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 21 then
    if j.val ≤ 13 then
      29
    else
      28
  else
    if j.val ≤ 24 then
      27
    else
      31

def coreSelector158_8 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 19 then
    if j.val ≤ 11 then
      29
    else
      28
  else
    if j.val ≤ 23 then
      27
    else
      31

def coreSelector158_9 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 9 then
      29
    else
      28
  else
    if j.val ≤ 22 then
      27
    else
      31

def coreSelector158_10 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      29
    else
      28
  else
    if j.val ≤ 21 then
      27
    else
      31

def coreSelector158_11 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      29
    else
      28
  else
    if j.val ≤ 20 then
      27
    else
      31

def coreSelector158_12 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      29
    else
      28
  else
    if j.val ≤ 19 then
      27
    else
      if j.val ≤ 20 then
        26
      else
        31

def coreSelector158_13 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      29
    else
      28
  else
    if j.val ≤ 17 then
      27
    else
      if j.val ≤ 19 then
        26
      else
        31

def coreSelector158_14 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      28
    else
      27
  else
    if j.val ≤ 18 then
      26
    else
      if j.val ≤ 23 then
        31
      else
        25

def coreSelector158_15 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      28
    else
      27
  else
    if j.val ≤ 17 then
      26
    else
      if j.val ≤ 21 then
        31
      else
        25

def coreSelector158_16 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 16 then
    if j.val ≤ 3 then
      28
    else
      if j.val ≤ 11 then
        27
      else
        26
  else
    if j.val ≤ 19 then
      31
    else
      if j.val ≤ 24 then
        25
      else
        33

def coreSelector158_17 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 1 then
      28
    else
      if j.val ≤ 9 then
        27
      else
        26
  else
    if j.val ≤ 23 then
      if j.val ≤ 17 then
        31
      else
        25
    else
      if j.val ≤ 24 then
        33
      else
        32

def coreSelector158_18 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 14 then
    if j.val ≤ 7 then
      27
    else
      26
  else
    if j.val ≤ 15 then
      31
    else
      if j.val ≤ 22 then
        25
      else
        32

def coreSelector158_19 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      27
    else
      26
  else
    if j.val ≤ 21 then
      25
    else
      if j.val ≤ 22 then
        24
      else
        32

def coreSelector158_20 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      27
    else
      26
  else
    if j.val ≤ 19 then
      25
    else
      if j.val ≤ 21 then
        24
      else
        32

def coreSelector158_21 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      27
    else
      26
  else
    if j.val ≤ 17 then
      25
    else
      if j.val ≤ 20 then
        24
      else
        32

def coreSelector158_22 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 19 then
    if j.val ≤ 7 then
      26
    else
      if j.val ≤ 15 then
        25
      else
        24
  else
    if j.val ≤ 20 then
      23
    else
      if j.val ≤ 24 then
        32
      else
        36

def coreSelector158_23 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 5 then
      26
    else
      if j.val ≤ 13 then
        25
      else
        24
  else
    if j.val ≤ 19 then
      23
    else
      if j.val ≤ 23 then
        32
      else
        36

def coreSelector158_24 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 18 then
    if j.val ≤ 11 then
      if j.val ≤ 3 then
        26
      else
        25
    else
      if j.val ≤ 15 then
        24
      else
        23
  else
    if j.val ≤ 20 then
      if j.val ≤ 19 then
        32
      else
        22
    else
      if j.val ≤ 22 then
        32
      else
        36

def coreSelector158_25 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        26
      else
        25
    else
      if j.val ≤ 13 then
        24
      else
        23
  else
    if j.val ≤ 20 then
      if j.val ≤ 19 then
        22
      else
        21
    else
      if j.val ≤ 21 then
        32
      else
        36

def coreSelector158_26 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 11 then
      if j.val ≤ 7 then
        25
      else
        24
    else
      if j.val ≤ 15 then
        23
      else
        22
  else
    if j.val ≤ 20 then
      if j.val ≤ 19 then
        21
      else
        32
    else
      if j.val ≤ 24 then
        36
      else
        37

def coreSelector158_27 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 9 then
      if j.val ≤ 5 then
        25
      else
        24
    else
      if j.val ≤ 13 then
        23
      else
        22
  else
    if j.val ≤ 19 then
      if j.val ≤ 18 then
        21
      else
        32
    else
      if j.val ≤ 23 then
        36
      else
        if j.val ≤ 24 then
          37
        else
          35

def coreSelector158_28 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        25
      else
        24
    else
      if j.val ≤ 11 then
        23
      else
        22
  else
    if j.val ≤ 18 then
      if j.val ≤ 17 then
        21
      else
        32
    else
      if j.val ≤ 22 then
        36
      else
        if j.val ≤ 24 then
          35
        else
          34

def coreSelector158_29 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        25
      else
        24
    else
      if j.val ≤ 9 then
        23
      else
        22
  else
    if j.val ≤ 17 then
      if j.val ≤ 16 then
        21
      else
        32
    else
      if j.val ≤ 20 then
        36
      else
        if j.val ≤ 22 then
          35
        else
          34

def coreSelector158_30 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 16 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        24
      else
        23
    else
      if j.val ≤ 9 then
        22
      else
        if j.val ≤ 15 then
          21
        else
          32
  else
    if j.val ≤ 20 then
      if j.val ≤ 18 then
        36
      else
        35
    else
      if j.val ≤ 21 then
        34
      else
        if j.val ≤ 23 then
          4
        else
          17

def coreSelector158_31 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        24
      else
        23
    else
      if j.val ≤ 7 then
        22
      else
        if j.val ≤ 14 then
          21
        else
          32
  else
    if j.val ≤ 19 then
      if j.val ≤ 16 then
        6
      else
        if j.val ≤ 18 then
          35
        else
          34
    else
      if j.val ≤ 21 then
        4
      else
        if j.val ≤ 24 then
          17
        else
          3

def coreSelector158_32 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        23
      else
        22
    else
      if j.val ≤ 13 then
        21
      else
        if j.val ≤ 14 then
          20
        else
          6
  else
    if j.val ≤ 18 then
      if j.val ≤ 17 then
        5
      else
        18
    else
      if j.val ≤ 19 then
        4
      else
        if j.val ≤ 23 then
          17
        else
          16

def coreSelector158_33 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        23
      else
        22
    else
      if j.val ≤ 11 then
        21
      else
        20
  else
    if j.val ≤ 15 then
      if j.val ≤ 14 then
        19
      else
        5
    else
      if j.val ≤ 17 then
        18
      else
        if j.val ≤ 21 then
          17
        else
          16

def coreSelector158_34 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        22
      else
        21
    else
      if j.val ≤ 11 then
        20
      else
        19
  else
    if j.val ≤ 19 then
      if j.val ≤ 15 then
        18
      else
        17
    else
      if j.val ≤ 23 then
        16
      else
        15

def coreSelector158_35 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 9 then
      if j.val ≤ 7 then
        21
      else
        20
    else
      if j.val ≤ 11 then
        19
      else
        18
  else
    if j.val ≤ 21 then
      if j.val ≤ 17 then
        17
      else
        16
    else
      if j.val ≤ 23 then
        15
      else
        14

def coreSelector158_36 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      if j.val ≤ 5 then
        21
      else
        20
    else
      if j.val ≤ 9 then
        19
      else
        18
  else
    if j.val ≤ 19 then
      if j.val ≤ 15 then
        17
      else
        16
    else
      if j.val ≤ 21 then
        15
      else
        if j.val ≤ 23 then
          14
        else
          13

def coreSelector158_37 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        21
      else
        20
    else
      if j.val ≤ 7 then
        19
      else
        if j.val ≤ 9 then
          18
        else
          17
  else
    if j.val ≤ 19 then
      if j.val ≤ 17 then
        16
      else
        15
    else
      if j.val ≤ 21 then
        14
      else
        if j.val ≤ 23 then
          13
        else
          12

def coreSelector158_38 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        21
      else
        20
    else
      if j.val ≤ 5 then
        19
      else
        if j.val ≤ 7 then
          18
        else
          17
  else
    if j.val ≤ 19 then
      if j.val ≤ 15 then
        16
      else
        if j.val ≤ 17 then
          15
        else
          14
    else
      if j.val ≤ 21 then
        13
      else
        if j.val ≤ 23 then
          12
        else
          11

def coreSelector158_39 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        20
      else
        19
    else
      if j.val ≤ 5 then
        18
      else
        if j.val ≤ 9 then
          17
        else
          16
  else
    if j.val ≤ 19 then
      if j.val ≤ 15 then
        15
      else
        if j.val ≤ 17 then
          14
        else
          13
    else
      if j.val ≤ 21 then
        12
      else
        if j.val ≤ 23 then
          11
        else
          10

def coreSelector158_40 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        19
      else
        18
    else
      if j.val ≤ 7 then
        17
      else
        if j.val ≤ 11 then
          16
        else
          15
  else
    if j.val ≤ 19 then
      if j.val ≤ 15 then
        14
      else
        if j.val ≤ 17 then
          13
        else
          12
    else
      if j.val ≤ 21 then
        11
      else
        if j.val ≤ 23 then
          10
        else
          9

def coreSelector158_41 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        18
      else
        17
    else
      if j.val ≤ 9 then
        16
      else
        if j.val ≤ 11 then
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
        if j.val ≤ 21 then
          10
        else
          9

def coreSelector158_42 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        17
      else
        16
    else
      if j.val ≤ 9 then
        15
      else
        14
  else
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        13
      else
        12
    else
      if j.val ≤ 17 then
        11
      else
        if j.val ≤ 19 then
          10
        else
          9

def coreSelector158_43 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        17
      else
        16
    else
      if j.val ≤ 7 then
        15
      else
        14
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        13
      else
        12
    else
      if j.val ≤ 15 then
        11
      else
        if j.val ≤ 17 then
          10
        else
          9

def coreSelector158_44 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        16
      else
        15
    else
      if j.val ≤ 7 then
        14
      else
        13
  else
    if j.val ≤ 13 then
      if j.val ≤ 11 then
        12
      else
        11
    else
      if j.val ≤ 15 then
        10
      else
        9

def coreSelector158_45 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        16
      else
        15
    else
      if j.val ≤ 5 then
        14
      else
        13
  else
    if j.val ≤ 11 then
      if j.val ≤ 9 then
        12
      else
        11
    else
      if j.val ≤ 13 then
        10
      else
        if j.val ≤ 24 then
          9
        else
          2

def coreSelector158_46 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        15
      else
        14
    else
      if j.val ≤ 5 then
        13
      else
        12
  else
    if j.val ≤ 11 then
      if j.val ≤ 9 then
        11
      else
        10
    else
      if j.val ≤ 23 then
        9
      else
        2

def coreSelector158_47 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      14
    else
      if j.val ≤ 3 then
        13
      else
        12
  else
    if j.val ≤ 9 then
      if j.val ≤ 7 then
        11
      else
        10
    else
      if j.val ≤ 22 then
        9
      else
        2

def coreSelector158_48 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      13
    else
      if j.val ≤ 3 then
        12
      else
        11
  else
    if j.val ≤ 21 then
      if j.val ≤ 7 then
        10
      else
        9
    else
      if j.val ≤ 23 then
        2
      else
        1

def coreSelector158_49 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      12
    else
      if j.val ≤ 3 then
        11
      else
        10
  else
    if j.val ≤ 21 then
      if j.val ≤ 20 then
        9
      else
        2
    else
      if j.val ≤ 23 then
        1
      else
        0

def coreSelector158_50 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 19 then
    if j.val ≤ 1 then
      11
    else
      if j.val ≤ 3 then
        10
      else
        9
  else
    if j.val ≤ 20 then
      8
    else
      if j.val ≤ 21 then
        1
      else
        0

def coreSelector158_51 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 1 then
      10
    else
      9
  else
    if j.val ≤ 19 then
      8
    else
      if j.val ≤ 20 then
        7
      else
        0

def coreSelector158_52 (j : Fin 26) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 15 then
      9
    else
      8
  else
    if j.val ≤ 19 then
      7
    else
      0

def coreSelector158 (b : Fin 53) (j : Fin 26) : Fin 38 :=
  if b.val ≤ 25 then
    if b.val ≤ 12 then
      if b.val ≤ 5 then
        if b.val ≤ 2 then
          if b.val ≤ 0 then
            coreSelector158_0 j
          else
            if b.val ≤ 1 then
              coreSelector158_1 j
            else
              coreSelector158_2 j
        else
          if b.val ≤ 3 then
            coreSelector158_3 j
          else
            if b.val ≤ 4 then
              coreSelector158_4 j
            else
              coreSelector158_5 j
      else
        if b.val ≤ 8 then
          if b.val ≤ 6 then
            coreSelector158_6 j
          else
            if b.val ≤ 7 then
              coreSelector158_7 j
            else
              coreSelector158_8 j
        else
          if b.val ≤ 10 then
            if b.val ≤ 9 then
              coreSelector158_9 j
            else
              coreSelector158_10 j
          else
            if b.val ≤ 11 then
              coreSelector158_11 j
            else
              coreSelector158_12 j
    else
      if b.val ≤ 18 then
        if b.val ≤ 15 then
          if b.val ≤ 13 then
            coreSelector158_13 j
          else
            if b.val ≤ 14 then
              coreSelector158_14 j
            else
              coreSelector158_15 j
        else
          if b.val ≤ 16 then
            coreSelector158_16 j
          else
            if b.val ≤ 17 then
              coreSelector158_17 j
            else
              coreSelector158_18 j
      else
        if b.val ≤ 21 then
          if b.val ≤ 19 then
            coreSelector158_19 j
          else
            if b.val ≤ 20 then
              coreSelector158_20 j
            else
              coreSelector158_21 j
        else
          if b.val ≤ 23 then
            if b.val ≤ 22 then
              coreSelector158_22 j
            else
              coreSelector158_23 j
          else
            if b.val ≤ 24 then
              coreSelector158_24 j
            else
              coreSelector158_25 j
  else
    if b.val ≤ 38 then
      if b.val ≤ 31 then
        if b.val ≤ 28 then
          if b.val ≤ 26 then
            coreSelector158_26 j
          else
            if b.val ≤ 27 then
              coreSelector158_27 j
            else
              coreSelector158_28 j
        else
          if b.val ≤ 29 then
            coreSelector158_29 j
          else
            if b.val ≤ 30 then
              coreSelector158_30 j
            else
              coreSelector158_31 j
      else
        if b.val ≤ 34 then
          if b.val ≤ 32 then
            coreSelector158_32 j
          else
            if b.val ≤ 33 then
              coreSelector158_33 j
            else
              coreSelector158_34 j
        else
          if b.val ≤ 36 then
            if b.val ≤ 35 then
              coreSelector158_35 j
            else
              coreSelector158_36 j
          else
            if b.val ≤ 37 then
              coreSelector158_37 j
            else
              coreSelector158_38 j
    else
      if b.val ≤ 45 then
        if b.val ≤ 41 then
          if b.val ≤ 39 then
            coreSelector158_39 j
          else
            if b.val ≤ 40 then
              coreSelector158_40 j
            else
              coreSelector158_41 j
        else
          if b.val ≤ 43 then
            if b.val ≤ 42 then
              coreSelector158_42 j
            else
              coreSelector158_43 j
          else
            if b.val ≤ 44 then
              coreSelector158_44 j
            else
              coreSelector158_45 j
      else
        if b.val ≤ 48 then
          if b.val ≤ 46 then
            coreSelector158_46 j
          else
            if b.val ≤ 47 then
              coreSelector158_47 j
            else
              coreSelector158_48 j
        else
          if b.val ≤ 50 then
            if b.val ≤ 49 then
              coreSelector158_49 j
            else
              coreSelector158_50 j
          else
            if b.val ≤ 51 then
              coreSelector158_51 j
            else
              coreSelector158_52 j
def coreMetadataChunks158 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩, ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩]
  | _ => [⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨153, [3, 3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨147, [3, 7, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨135, [3, 3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]
end Erdos883Verified
