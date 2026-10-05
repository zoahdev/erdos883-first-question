import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData174 : List CoreOddData :=
  [⟨1, [], [0, 0, 0, 0, 0]⟩,
   ⟨173, [173], [0, 0, 0, 0, 0]⟩,
   ⟨167, [167], [0, 0, 0, 0, 0]⟩,
   ⟨163, [163], [0, 0, 0, 0, 0]⟩,
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
   ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩,
   ⟨11, [11], [0, 0, 0, 0, 1]⟩,
   ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩,
   ⟨7, [7], [0, 0, 0, 1, 2]⟩,
   ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩,
   ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩,
   ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩,
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
   ⟨159, [3, 53], [0, 1, 2, 4, 8]⟩,
   ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩,
   ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩,
   ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩,
   ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩,
   ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩,
   ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩,
   ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩,
   ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩,
   ⟨171, [3, 3, 19], [0, 1, 2, 4, 8]⟩,
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
   ⟨165, [3, 5, 11], [0, 1, 3, 6, 13]⟩,
   ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreResources174 (i : Fin 38) : CoreResourceData :=
  if i.val ≤ 18 then
    if i.val ≤ 8 then
      if i.val ≤ 3 then
        if i.val ≤ 1 then
          if i.val ≤ 0 then
            ⟨19, 0, 157, false⟩
          else
            ⟨20, 0, 156, false⟩
        else
          if i.val ≤ 2 then
            ⟨24, 0, 155, false⟩
          else
            ⟨42, 0, 115, false⟩
      else
        if i.val ≤ 5 then
          if i.val ≤ 4 then
            ⟨43, 0, 109, false⟩
          else
            ⟨44, 0, 108, false⟩
        else
          if i.val ≤ 6 then
            ⟨45, 0, 107, false⟩
          else
            if i.val ≤ 7 then
              ⟨20, 0, 78, true⟩
            else
              ⟨29, 0, 77, true⟩
    else
      if i.val ≤ 13 then
        if i.val ≤ 10 then
          if i.val ≤ 9 then
            ⟨30, 0, 76, true⟩
          else
            ⟨32, 0, 75, true⟩
        else
          if i.val ≤ 11 then
            ⟨33, 0, 74, true⟩
          else
            if i.val ≤ 12 then
              ⟨34, 0, 72, true⟩
            else
              ⟨35, 0, 71, true⟩
      else
        if i.val ≤ 15 then
          if i.val ≤ 14 then
            ⟨37, 0, 69, true⟩
          else
            ⟨39, 0, 66, true⟩
        else
          if i.val ≤ 16 then
            ⟨41, 0, 62, true⟩
          else
            if i.val ≤ 17 then
              ⟨42, 0, 56, true⟩
            else
              ⟨43, 0, 53, true⟩
  else
    if i.val ≤ 27 then
      if i.val ≤ 22 then
        if i.val ≤ 20 then
          if i.val ≤ 19 then
            ⟨45, 0, 52, true⟩
          else
            ⟨48, 0, 51, true⟩
        else
          if i.val ≤ 21 then
            ⟨50, 0, 50, true⟩
          else
            ⟨52, 0, 48, true⟩
      else
        if i.val ≤ 24 then
          if i.val ≤ 23 then
            ⟨53, 0, 47, true⟩
          else
            ⟨55, 0, 46, true⟩
        else
          if i.val ≤ 25 then
            ⟨58, 0, 45, true⟩
          else
            if i.val ≤ 26 then
              ⟨62, 0, 37, true⟩
            else
              ⟨66, 0, 36, true⟩
    else
      if i.val ≤ 32 then
        if i.val ≤ 29 then
          if i.val ≤ 28 then
            ⟨70, 0, 35, true⟩
          else
            ⟨85, 0, 34, true⟩
        else
          if i.val ≤ 30 then
            ⟨87, 0, 31, true⟩
          else
            if i.val ≤ 31 then
              ⟨67, 1, 45, true⟩
            else
              ⟨57, 2, 52, true⟩
      else
        if i.val ≤ 34 then
          if i.val ≤ 33 then
            ⟨59, 2, 50, true⟩
          else
            ⟨48, 3, 60, true⟩
        else
          if i.val ≤ 35 then
            ⟨49, 3, 58, true⟩
          else
            if i.val ≤ 36 then
              ⟨54, 3, 56, true⟩
            else
              ⟨54, 4, 57, true⟩

def coreChunks174_0 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩]

def coreChunks174_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨79, [79], [0, 0, 0, 0, 0]⟩]

def coreChunks174_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩]

def coreChunks174_3 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩]
  | _ => [⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩]

def coreChunks174_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨161, [7, 23], [0, 0, 0, 1, 2]⟩]

def coreChunks174_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨133, [7, 19], [0, 0, 0, 1, 2]⟩]

def coreChunks174_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]

def coreChunks174_7 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩]

def coreChunks174_8 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩]

def coreChunks174_9 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨37, [37], [0, 0, 0, 0, 0]⟩]

def coreChunks174_10 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]

def coreChunks174_11 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks174_12 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩]

def coreChunks174_13 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks174_14 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩]

def coreChunks174_15 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩]

def coreChunks174_16 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩]

def coreChunks174_17 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨143, [11, 13], [0, 0, 0, 0, 1]⟩]

def coreChunks174_18 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨161, [7, 23], [0, 0, 0, 1, 2]⟩]

def coreChunks174_19 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]

def coreChunks174_20 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks174_21 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩]

def coreChunks174_22 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩]

def coreChunks174_23 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨115, [5, 23], [0, 0, 1, 2, 4]⟩]

def coreChunks174_24 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks174_25 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks174_26 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks174_27 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨159, [3, 53], [0, 1, 2, 4, 8]⟩, ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩, ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩]

def coreChunks174_28 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩]

def coreChunks174_29 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨171, [3, 3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨153, [3, 3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨147, [3, 7, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨135, [3, 3, 3, 5], [0, 1, 3, 6, 12]⟩]

def coreChunks174_30 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨165, [3, 5, 11], [0, 1, 3, 6, 13]⟩, ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreChunks174_31 (c : Fin 5) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]
  | 3 => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨159, [3, 53], [0, 1, 2, 4, 8]⟩, ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩]
  | _ => [⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩]

def coreChunks174_32 (c : Fin 4) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩]

def coreChunks174_33 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩]

def coreChunks174_34 (c : Fin 3) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks174_35 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩]

def coreChunks174_36 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩]

def coreChunks174_37 (c : Fin 4) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩]

def coreSelector174_0 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 3 then
    30
  else
    29

def coreSelector174_1 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 1 then
    30
  else
    29

def coreSelector174_2 (j : Fin 29) : Fin 38 :=
  29

def coreSelector174_3 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 27 then
    29
  else
    28

def coreSelector174_4 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 25 then
    29
  else
    28

def coreSelector174_5 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 23 then
    29
  else
    28

def coreSelector174_6 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 21 then
    29
  else
    28

def coreSelector174_7 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 19 then
    29
  else
    if j.val ≤ 27 then
      28
    else
      27

def coreSelector174_8 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 25 then
    if j.val ≤ 17 then
      29
    else
      28
  else
    if j.val ≤ 27 then
      27
    else
      31

def coreSelector174_9 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 23 then
    if j.val ≤ 15 then
      29
    else
      28
  else
    if j.val ≤ 26 then
      27
    else
      31

def coreSelector174_10 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 21 then
    if j.val ≤ 13 then
      29
    else
      28
  else
    if j.val ≤ 25 then
      27
    else
      31

def coreSelector174_11 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 19 then
    if j.val ≤ 11 then
      29
    else
      28
  else
    if j.val ≤ 24 then
      27
    else
      31

def coreSelector174_12 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 9 then
      29
    else
      28
  else
    if j.val ≤ 23 then
      27
    else
      31

def coreSelector174_13 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      29
    else
      28
  else
    if j.val ≤ 22 then
      27
    else
      31

def coreSelector174_14 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      29
    else
      28
  else
    if j.val ≤ 21 then
      27
    else
      if j.val ≤ 22 then
        26
      else
        31

def coreSelector174_15 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 19 then
    if j.val ≤ 3 then
      29
    else
      if j.val ≤ 11 then
        28
      else
        27
  else
    if j.val ≤ 21 then
      26
    else
      if j.val ≤ 27 then
        31
      else
        25

def coreSelector174_16 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 1 then
      29
    else
      if j.val ≤ 9 then
        28
      else
        27
  else
    if j.val ≤ 20 then
      26
    else
      if j.val ≤ 25 then
        31
      else
        25

def coreSelector174_17 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 19 then
    if j.val ≤ 7 then
      28
    else
      if j.val ≤ 15 then
        27
      else
        26
  else
    if j.val ≤ 23 then
      31
    else
      if j.val ≤ 27 then
        25
      else
        33

def coreSelector174_18 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 18 then
    if j.val ≤ 5 then
      28
    else
      if j.val ≤ 13 then
        27
      else
        26
  else
    if j.val ≤ 21 then
      31
    else
      if j.val ≤ 26 then
        25
      else
        33

def coreSelector174_19 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 3 then
      28
    else
      if j.val ≤ 11 then
        27
      else
        26
  else
    if j.val ≤ 25 then
      if j.val ≤ 19 then
        31
      else
        25
    else
      if j.val ≤ 26 then
        24
      else
        32

def coreSelector174_20 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 16 then
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
      if j.val ≤ 25 then
        24
      else
        32

def coreSelector174_21 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      27
    else
      26
  else
    if j.val ≤ 21 then
      25
    else
      if j.val ≤ 24 then
        24
      else
        32

def coreSelector174_22 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 19 then
    if j.val ≤ 5 then
      27
    else
      if j.val ≤ 13 then
        26
      else
        25
  else
    if j.val ≤ 23 then
      24
    else
      if j.val ≤ 24 then
        23
      else
        32

def coreSelector174_23 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 3 then
      27
    else
      if j.val ≤ 11 then
        26
      else
        25
  else
    if j.val ≤ 23 then
      if j.val ≤ 21 then
        24
      else
        23
    else
      if j.val ≤ 24 then
        22
      else
        32

def coreSelector174_24 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 19 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        27
      else
        26
    else
      if j.val ≤ 15 then
        25
      else
        24
  else
    if j.val ≤ 23 then
      if j.val ≤ 21 then
        23
      else
        22
    else
      if j.val ≤ 27 then
        32
      else
        36

def coreSelector174_25 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 19 then
    if j.val ≤ 13 then
      if j.val ≤ 7 then
        26
      else
        25
    else
      if j.val ≤ 17 then
        24
      else
        23
  else
    if j.val ≤ 23 then
      if j.val ≤ 22 then
        22
      else
        32
    else
      if j.val ≤ 24 then
        21
      else
        if j.val ≤ 26 then
          32
        else
          36

def coreSelector174_26 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 11 then
      if j.val ≤ 5 then
        26
      else
        25
    else
      if j.val ≤ 15 then
        24
      else
        23
  else
    if j.val ≤ 23 then
      if j.val ≤ 21 then
        22
      else
        21
    else
      if j.val ≤ 25 then
        32
      else
        36

def coreSelector174_27 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 9 then
      if j.val ≤ 3 then
        26
      else
        25
    else
      if j.val ≤ 13 then
        24
      else
        23
  else
    if j.val ≤ 22 then
      if j.val ≤ 19 then
        22
      else
        21
    else
      if j.val ≤ 24 then
        32
      else
        36

def coreSelector174_28 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 7 then
      if j.val ≤ 1 then
        26
      else
        25
    else
      if j.val ≤ 11 then
        24
      else
        if j.val ≤ 13 then
          23
        else
          22
  else
    if j.val ≤ 22 then
      if j.val ≤ 21 then
        21
      else
        20
    else
      if j.val ≤ 23 then
        32
      else
        if j.val ≤ 27 then
          36
        else
          37

def coreSelector174_29 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 9 then
      if j.val ≤ 5 then
        25
      else
        24
    else
      if j.val ≤ 11 then
        23
      else
        22
  else
    if j.val ≤ 21 then
      if j.val ≤ 19 then
        21
      else
        20
    else
      if j.val ≤ 22 then
        32
      else
        if j.val ≤ 26 then
          36
        else
          35

def coreSelector174_30 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        25
      else
        24
    else
      if j.val ≤ 9 then
        23
      else
        if j.val ≤ 13 then
          22
        else
          21
  else
    if j.val ≤ 21 then
      if j.val ≤ 20 then
        20
      else
        32
    else
      if j.val ≤ 24 then
        36
      else
        if j.val ≤ 26 then
          35
        else
          34

def coreSelector174_31 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        25
      else
        24
    else
      if j.val ≤ 7 then
        23
      else
        if j.val ≤ 11 then
          22
        else
          21
  else
    if j.val ≤ 20 then
      if j.val ≤ 19 then
        20
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

def coreSelector174_32 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 18 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        24
      else
        23
    else
      if j.val ≤ 9 then
        22
      else
        if j.val ≤ 13 then
          21
        else
          20
  else
    if j.val ≤ 22 then
      if j.val ≤ 19 then
        32
      else
        if j.val ≤ 20 then
          36
        else
          35
    else
      if j.val ≤ 25 then
        34
      else
        if j.val ≤ 27 then
          3
        else
          16

def coreSelector174_33 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        24
      else
        23
    else
      if j.val ≤ 7 then
        22
      else
        if j.val ≤ 11 then
          21
        else
          20
  else
    if j.val ≤ 20 then
      if j.val ≤ 18 then
        19
      else
        if j.val ≤ 19 then
          6
        else
          5
    else
      if j.val ≤ 23 then
        34
      else
        if j.val ≤ 25 then
          3
        else
          16

def coreSelector174_34 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        23
      else
        22
    else
      if j.val ≤ 9 then
        21
      else
        if j.val ≤ 15 then
          20
        else
          19
  else
    if j.val ≤ 21 then
      if j.val ≤ 19 then
        5
      else
        4
    else
      if j.val ≤ 23 then
        3
      else
        if j.val ≤ 27 then
          16
        else
          15

def coreSelector174_35 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 17 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        22
      else
        21
    else
      if j.val ≤ 13 then
        20
      else
        if j.val ≤ 16 then
          19
        else
          5
  else
    if j.val ≤ 20 then
      if j.val ≤ 19 then
        4
      else
        17
    else
      if j.val ≤ 21 then
        3
      else
        if j.val ≤ 25 then
          16
        else
          15

def coreSelector174_36 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 16 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        22
      else
        21
    else
      if j.val ≤ 11 then
        20
      else
        if j.val ≤ 15 then
          19
        else
          18
  else
    if j.val ≤ 19 then
      if j.val ≤ 17 then
        4
      else
        17
    else
      if j.val ≤ 23 then
        16
      else
        if j.val ≤ 27 then
          15
        else
          14

def coreSelector174_37 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 9 then
      if j.val ≤ 3 then
        21
      else
        20
    else
      if j.val ≤ 13 then
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
      if j.val ≤ 25 then
        15
      else
        14

def coreSelector174_38 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 1 then
        21
      else
        20
    else
      if j.val ≤ 11 then
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
      if j.val ≤ 23 then
        15
      else
        if j.val ≤ 27 then
          14
        else
          13

def coreSelector174_39 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 9 then
      if j.val ≤ 5 then
        20
      else
        19
    else
      if j.val ≤ 11 then
        18
      else
        17
  else
    if j.val ≤ 21 then
      if j.val ≤ 17 then
        16
      else
        15
    else
      if j.val ≤ 25 then
        14
      else
        if j.val ≤ 27 then
          13
        else
          12

def coreSelector174_40 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        20
      else
        19
    else
      if j.val ≤ 9 then
        18
      else
        if j.val ≤ 11 then
          17
        else
          16
  else
    if j.val ≤ 23 then
      if j.val ≤ 19 then
        15
      else
        14
    else
      if j.val ≤ 25 then
        13
      else
        if j.val ≤ 27 then
          12
        else
          11

def coreSelector174_41 (j : Fin 29) : Fin 38 :=
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
        if j.val ≤ 9 then
          17
        else
          16
  else
    if j.val ≤ 23 then
      if j.val ≤ 17 then
        15
      else
        if j.val ≤ 21 then
          14
        else
          13
    else
      if j.val ≤ 25 then
        12
      else
        if j.val ≤ 27 then
          11
        else
          10

def coreSelector174_42 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
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
    if j.val ≤ 21 then
      if j.val ≤ 19 then
        14
      else
        13
    else
      if j.val ≤ 23 then
        12
      else
        if j.val ≤ 25 then
          11
        else
          10

def coreSelector174_43 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        19
      else
        18
    else
      if j.val ≤ 5 then
        17
      else
        if j.val ≤ 9 then
          16
        else
          15
  else
    if j.val ≤ 21 then
      if j.val ≤ 17 then
        14
      else
        if j.val ≤ 19 then
          13
        else
          12
    else
      if j.val ≤ 23 then
        11
      else
        if j.val ≤ 27 then
          10
        else
          9

def coreSelector174_44 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        18
      else
        17
    else
      if j.val ≤ 7 then
        16
      else
        if j.val ≤ 11 then
          15
        else
          14
  else
    if j.val ≤ 21 then
      if j.val ≤ 17 then
        13
      else
        if j.val ≤ 19 then
          12
        else
          11
    else
      if j.val ≤ 25 then
        10
      else
        if j.val ≤ 27 then
          9
        else
          8

def coreSelector174_45 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 15 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        17
      else
        16
    else
      if j.val ≤ 9 then
        15
      else
        if j.val ≤ 13 then
          14
        else
          13
  else
    if j.val ≤ 19 then
      if j.val ≤ 17 then
        12
      else
        11
    else
      if j.val ≤ 23 then
        10
      else
        if j.val ≤ 25 then
          9
        else
          8

def coreSelector174_46 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        16
      else
        15
    else
      if j.val ≤ 11 then
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
      if j.val ≤ 21 then
        10
      else
        if j.val ≤ 23 then
          9
        else
          8

def coreSelector174_47 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        16
      else
        15
    else
      if j.val ≤ 9 then
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
      if j.val ≤ 19 then
        10
      else
        if j.val ≤ 21 then
          9
        else
          8

def coreSelector174_48 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 11 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        15
      else
        14
    else
      if j.val ≤ 9 then
        13
      else
        12
  else
    if j.val ≤ 17 then
      if j.val ≤ 13 then
        11
      else
        10
    else
      if j.val ≤ 19 then
        9
      else
        8

def coreSelector174_49 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        15
      else
        14
    else
      if j.val ≤ 7 then
        13
      else
        12
  else
    if j.val ≤ 15 then
      if j.val ≤ 11 then
        11
      else
        10
    else
      if j.val ≤ 17 then
        9
      else
        if j.val ≤ 27 then
          8
        else
          2

def coreSelector174_50 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 9 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        14
      else
        13
    else
      if j.val ≤ 7 then
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
      if j.val ≤ 26 then
        8
      else
        2

def coreSelector174_51 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 7 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        14
      else
        13
    else
      if j.val ≤ 5 then
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
      if j.val ≤ 25 then
        8
      else
        2

def coreSelector174_52 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 5 then
    if j.val ≤ 1 then
      13
    else
      if j.val ≤ 3 then
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
      if j.val ≤ 24 then
        8
      else
        2

def coreSelector174_53 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      12
    else
      if j.val ≤ 3 then
        11
      else
        10
  else
    if j.val ≤ 23 then
      if j.val ≤ 9 then
        9
      else
        8
    else
      if j.val ≤ 27 then
        2
      else
        1

def coreSelector174_54 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 7 then
    if j.val ≤ 1 then
      11
    else
      if j.val ≤ 5 then
        10
      else
        9
  else
    if j.val ≤ 25 then
      if j.val ≤ 22 then
        8
      else
        2
    else
      if j.val ≤ 27 then
        1
      else
        0

def coreSelector174_55 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 21 then
    if j.val ≤ 3 then
      10
    else
      if j.val ≤ 5 then
        9
      else
        8
  else
    if j.val ≤ 23 then
      2
    else
      if j.val ≤ 25 then
        1
      else
        0

def coreSelector174_56 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 20 then
    if j.val ≤ 1 then
      10
    else
      if j.val ≤ 3 then
        9
      else
        8
  else
    if j.val ≤ 21 then
      2
    else
      if j.val ≤ 23 then
        1
      else
        0

def coreSelector174_57 (j : Fin 29) : Fin 38 :=
  if j.val ≤ 19 then
    if j.val ≤ 1 then
      9
    else
      8
  else
    if j.val ≤ 20 then
      7
    else
      if j.val ≤ 21 then
        1
      else
        0

def coreSelector174 (b : Fin 58) (j : Fin 29) : Fin 38 :=
  if b.val ≤ 28 then
    if b.val ≤ 13 then
      if b.val ≤ 6 then
        if b.val ≤ 2 then
          if b.val ≤ 0 then
            coreSelector174_0 j
          else
            if b.val ≤ 1 then
              coreSelector174_1 j
            else
              coreSelector174_2 j
        else
          if b.val ≤ 4 then
            if b.val ≤ 3 then
              coreSelector174_3 j
            else
              coreSelector174_4 j
          else
            if b.val ≤ 5 then
              coreSelector174_5 j
            else
              coreSelector174_6 j
      else
        if b.val ≤ 9 then
          if b.val ≤ 7 then
            coreSelector174_7 j
          else
            if b.val ≤ 8 then
              coreSelector174_8 j
            else
              coreSelector174_9 j
        else
          if b.val ≤ 11 then
            if b.val ≤ 10 then
              coreSelector174_10 j
            else
              coreSelector174_11 j
          else
            if b.val ≤ 12 then
              coreSelector174_12 j
            else
              coreSelector174_13 j
    else
      if b.val ≤ 20 then
        if b.val ≤ 16 then
          if b.val ≤ 14 then
            coreSelector174_14 j
          else
            if b.val ≤ 15 then
              coreSelector174_15 j
            else
              coreSelector174_16 j
        else
          if b.val ≤ 18 then
            if b.val ≤ 17 then
              coreSelector174_17 j
            else
              coreSelector174_18 j
          else
            if b.val ≤ 19 then
              coreSelector174_19 j
            else
              coreSelector174_20 j
      else
        if b.val ≤ 24 then
          if b.val ≤ 22 then
            if b.val ≤ 21 then
              coreSelector174_21 j
            else
              coreSelector174_22 j
          else
            if b.val ≤ 23 then
              coreSelector174_23 j
            else
              coreSelector174_24 j
        else
          if b.val ≤ 26 then
            if b.val ≤ 25 then
              coreSelector174_25 j
            else
              coreSelector174_26 j
          else
            if b.val ≤ 27 then
              coreSelector174_27 j
            else
              coreSelector174_28 j
  else
    if b.val ≤ 42 then
      if b.val ≤ 35 then
        if b.val ≤ 31 then
          if b.val ≤ 29 then
            coreSelector174_29 j
          else
            if b.val ≤ 30 then
              coreSelector174_30 j
            else
              coreSelector174_31 j
        else
          if b.val ≤ 33 then
            if b.val ≤ 32 then
              coreSelector174_32 j
            else
              coreSelector174_33 j
          else
            if b.val ≤ 34 then
              coreSelector174_34 j
            else
              coreSelector174_35 j
      else
        if b.val ≤ 38 then
          if b.val ≤ 36 then
            coreSelector174_36 j
          else
            if b.val ≤ 37 then
              coreSelector174_37 j
            else
              coreSelector174_38 j
        else
          if b.val ≤ 40 then
            if b.val ≤ 39 then
              coreSelector174_39 j
            else
              coreSelector174_40 j
          else
            if b.val ≤ 41 then
              coreSelector174_41 j
            else
              coreSelector174_42 j
    else
      if b.val ≤ 49 then
        if b.val ≤ 45 then
          if b.val ≤ 43 then
            coreSelector174_43 j
          else
            if b.val ≤ 44 then
              coreSelector174_44 j
            else
              coreSelector174_45 j
        else
          if b.val ≤ 47 then
            if b.val ≤ 46 then
              coreSelector174_46 j
            else
              coreSelector174_47 j
          else
            if b.val ≤ 48 then
              coreSelector174_48 j
            else
              coreSelector174_49 j
      else
        if b.val ≤ 53 then
          if b.val ≤ 51 then
            if b.val ≤ 50 then
              coreSelector174_50 j
            else
              coreSelector174_51 j
          else
            if b.val ≤ 52 then
              coreSelector174_52 j
            else
              coreSelector174_53 j
        else
          if b.val ≤ 55 then
            if b.val ≤ 54 then
              coreSelector174_54 j
            else
              coreSelector174_55 j
          else
            if b.val ≤ 56 then
              coreSelector174_56 j
            else
              coreSelector174_57 j
def coreMetadataChunks174 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨159, [3, 53], [0, 1, 2, 4, 8]⟩, ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩]
  | _ => [⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨171, [3, 3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨153, [3, 3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨147, [3, 7, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨135, [3, 3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨165, [3, 5, 11], [0, 1, 3, 6, 13]⟩, ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]
end Erdos883Verified
