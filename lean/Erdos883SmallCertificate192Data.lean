import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData192 : List CoreOddData :=
  [⟨1, [], [0, 0, 0, 0, 0]⟩,
   ⟨191, [191], [0, 0, 0, 0, 0]⟩,
   ⟨181, [181], [0, 0, 0, 0, 0]⟩,
   ⟨179, [179], [0, 0, 0, 0, 0]⟩,
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
   ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩,
   ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩,
   ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩,
   ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩,
   ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩,
   ⟨5, [5], [0, 0, 1, 2, 4]⟩,
   ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩,
   ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩,
   ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩,
   ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩,
   ⟨185, [5, 37], [0, 0, 1, 2, 4]⟩,
   ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩,
   ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩,
   ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩,
   ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩,
   ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩,
   ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩,
   ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩,
   ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩,
   ⟨175, [5, 5, 7], [0, 0, 1, 3, 6]⟩,
   ⟨3, [3], [0, 1, 2, 4, 8]⟩,
   ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨183, [3, 61], [0, 1, 2, 4, 8]⟩,
   ⟨177, [3, 59], [0, 1, 2, 4, 8]⟩,
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
   ⟨189, [3, 3, 3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩,
   ⟨135, [3, 3, 3, 5], [0, 1, 3, 6, 12]⟩,
   ⟨165, [3, 5, 11], [0, 1, 3, 6, 13]⟩,
   ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreResources192 (i : Fin 42) : CoreResourceData :=
  if i.val ≤ 20 then
    if i.val ≤ 9 then
      if i.val ≤ 4 then
        if i.val ≤ 1 then
          if i.val ≤ 0 then
            ⟨21, 0, 173, false⟩
          else
            ⟨22, 0, 172, false⟩
        else
          if i.val ≤ 2 then
            ⟨27, 0, 171, false⟩
          else
            if i.val ≤ 3 then
              ⟨43, 0, 137, false⟩
            else
              ⟨45, 0, 128, false⟩
      else
        if i.val ≤ 6 then
          if i.val ≤ 5 then
            ⟨46, 0, 126, false⟩
          else
            ⟨47, 0, 120, false⟩
        else
          if i.val ≤ 7 then
            ⟨48, 0, 118, false⟩
          else
            if i.val ≤ 8 then
              ⟨22, 0, 86, true⟩
            else
              ⟨30, 0, 85, true⟩
    else
      if i.val ≤ 14 then
        if i.val ≤ 11 then
          if i.val ≤ 10 then
            ⟨31, 0, 84, true⟩
          else
            ⟨34, 0, 83, true⟩
        else
          if i.val ≤ 12 then
            ⟨35, 0, 82, true⟩
          else
            if i.val ≤ 13 then
              ⟨36, 0, 81, true⟩
            else
              ⟨37, 0, 80, true⟩
      else
        if i.val ≤ 17 then
          if i.val ≤ 15 then
            ⟨38, 0, 78, true⟩
          else
            if i.val ≤ 16 then
              ⟨40, 0, 76, true⟩
            else
              ⟨42, 0, 74, true⟩
        else
          if i.val ≤ 18 then
            ⟨44, 0, 69, true⟩
          else
            if i.val ≤ 19 then
              ⟨45, 0, 64, true⟩
            else
              ⟨46, 0, 63, true⟩
  else
    if i.val ≤ 30 then
      if i.val ≤ 25 then
        if i.val ≤ 22 then
          if i.val ≤ 21 then
            ⟨47, 0, 60, true⟩
          else
            ⟨48, 0, 59, true⟩
        else
          if i.val ≤ 23 then
            ⟨49, 0, 58, true⟩
          else
            if i.val ≤ 24 then
              ⟨52, 0, 56, true⟩
            else
              ⟨54, 0, 55, true⟩
      else
        if i.val ≤ 27 then
          if i.val ≤ 26 then
            ⟨56, 0, 53, true⟩
          else
            ⟨58, 0, 52, true⟩
        else
          if i.val ≤ 28 then
            ⟨60, 0, 51, true⟩
          else
            if i.val ≤ 29 then
              ⟨64, 0, 50, true⟩
            else
              ⟨68, 0, 40, true⟩
    else
      if i.val ≤ 35 then
        if i.val ≤ 32 then
          if i.val ≤ 31 then
            ⟨72, 0, 39, true⟩
          else
            ⟨78, 0, 38, true⟩
        else
          if i.val ≤ 33 then
            ⟨94, 0, 37, true⟩
          else
            if i.val ≤ 34 then
              ⟨96, 0, 34, true⟩
            else
              ⟨75, 1, 50, true⟩
      else
        if i.val ≤ 38 then
          if i.val ≤ 36 then
            ⟨62, 2, 58, true⟩
          else
            if i.val ≤ 37 then
              ⟨64, 2, 55, true⟩
            else
              ⟨50, 3, 133, false⟩
        else
          if i.val ≤ 39 then
            ⟨52, 3, 66, true⟩
          else
            if i.val ≤ 40 then
              ⟨53, 3, 64, true⟩
            else
              ⟨58, 3, 63, true⟩

def coreChunks192_0 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩]

def coreChunks192_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨83, [83], [0, 0, 0, 0, 0]⟩]

def coreChunks192_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩]

def coreChunks192_3 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩]

def coreChunks192_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩]

def coreChunks192_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨143, [11, 13], [0, 0, 0, 0, 1]⟩]

def coreChunks192_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨161, [7, 23], [0, 0, 0, 1, 2]⟩]

def coreChunks192_7 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨133, [7, 19], [0, 0, 0, 1, 2]⟩]

def coreChunks192_8 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩]

def coreChunks192_9 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩]

def coreChunks192_10 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨43, [43], [0, 0, 0, 0, 0]⟩]

def coreChunks192_11 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩]

def coreChunks192_12 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨29, [29], [0, 0, 0, 0, 0]⟩]

def coreChunks192_13 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks192_14 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩]

def coreChunks192_15 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks192_16 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩]

def coreChunks192_17 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩]

def coreChunks192_18 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩]

def coreChunks192_19 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨187, [11, 17], [0, 0, 0, 0, 1]⟩]

def coreChunks192_20 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨143, [11, 13], [0, 0, 0, 0, 1]⟩]

def coreChunks192_21 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨161, [7, 23], [0, 0, 0, 1, 2]⟩]

def coreChunks192_22 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨133, [7, 19], [0, 0, 0, 1, 2]⟩]

def coreChunks192_23 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]

def coreChunks192_24 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks192_25 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩]

def coreChunks192_26 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨185, [5, 37], [0, 0, 1, 2, 4]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩]

def coreChunks192_27 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩]

def coreChunks192_28 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks192_29 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨175, [5, 5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks192_30 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks192_31 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨183, [3, 61], [0, 1, 2, 4, 8]⟩, ⟨177, [3, 59], [0, 1, 2, 4, 8]⟩, ⟨159, [3, 53], [0, 1, 2, 4, 8]⟩, ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩]

def coreChunks192_32 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩]

def coreChunks192_33 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨171, [3, 3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨153, [3, 3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨147, [3, 7, 7], [0, 1, 2, 5, 10]⟩, ⟨189, [3, 3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨135, [3, 3, 3, 5], [0, 1, 3, 6, 12]⟩]

def coreChunks192_34 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨165, [3, 5, 11], [0, 1, 3, 6, 13]⟩, ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreChunks192_35 (c : Fin 5) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩]
  | 3 => [⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨185, [5, 37], [0, 0, 1, 2, 4]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨175, [5, 5, 7], [0, 0, 1, 3, 6]⟩]
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨183, [3, 61], [0, 1, 2, 4, 8]⟩, ⟨177, [3, 59], [0, 1, 2, 4, 8]⟩, ⟨159, [3, 53], [0, 1, 2, 4, 8]⟩, ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩, ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩]

def coreChunks192_36 (c : Fin 4) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩]
  | _ => [⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨185, [5, 37], [0, 0, 1, 2, 4]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩]

def coreChunks192_37 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨175, [5, 5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks192_38 (c : Fin 4) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩]
  | _ => [⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩]

def coreChunks192_39 (c : Fin 4) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩]
  | _ => [⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks192_40 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩]

def coreChunks192_41 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨185, [5, 37], [0, 0, 1, 2, 4]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩]

def coreSelector192_0 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 3 then
    34
  else
    33

def coreSelector192_1 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 1 then
    34
  else
    33

def coreSelector192_2 (j : Fin 32) : Fin 42 :=
  33

def coreSelector192_3 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 29 then
    33
  else
    32

def coreSelector192_4 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 27 then
    33
  else
    32

def coreSelector192_5 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 25 then
    33
  else
    32

def coreSelector192_6 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 23 then
    33
  else
    32

def coreSelector192_7 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 21 then
    33
  else
    if j.val ≤ 30 then
      32
    else
      35

def coreSelector192_8 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    33
  else
    if j.val ≤ 29 then
      32
    else
      35

def coreSelector192_9 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 17 then
    33
  else
    if j.val ≤ 28 then
      32
    else
      35

def coreSelector192_10 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 27 then
    if j.val ≤ 15 then
      33
    else
      32
  else
    if j.val ≤ 28 then
      31
    else
      35

def coreSelector192_11 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 25 then
    if j.val ≤ 13 then
      33
    else
      32
  else
    if j.val ≤ 27 then
      31
    else
      35

def coreSelector192_12 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 23 then
    if j.val ≤ 11 then
      33
    else
      32
  else
    if j.val ≤ 26 then
      31
    else
      35

def coreSelector192_13 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 21 then
    if j.val ≤ 9 then
      33
    else
      32
  else
    if j.val ≤ 25 then
      31
    else
      35

def coreSelector192_14 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 7 then
      33
    else
      32
  else
    if j.val ≤ 24 then
      31
    else
      35

def coreSelector192_15 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 17 then
    if j.val ≤ 5 then
      33
    else
      32
  else
    if j.val ≤ 23 then
      31
    else
      35

def coreSelector192_16 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 15 then
    if j.val ≤ 3 then
      33
    else
      32
  else
    if j.val ≤ 22 then
      31
    else
      35

def coreSelector192_17 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 21 then
    if j.val ≤ 1 then
      33
    else
      if j.val ≤ 13 then
        32
      else
        31
  else
    if j.val ≤ 22 then
      30
    else
      if j.val ≤ 29 then
        35
      else
        29

def coreSelector192_18 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 11 then
      32
    else
      31
  else
    if j.val ≤ 21 then
      30
    else
      if j.val ≤ 27 then
        35
      else
        29

def coreSelector192_19 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 20 then
    if j.val ≤ 9 then
      32
    else
      if j.val ≤ 17 then
        31
      else
        30
  else
    if j.val ≤ 25 then
      35
    else
      if j.val ≤ 30 then
        29
      else
        37

def coreSelector192_20 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 7 then
      32
    else
      if j.val ≤ 15 then
        31
      else
        30
  else
    if j.val ≤ 23 then
      35
    else
      if j.val ≤ 29 then
        29
      else
        37

def coreSelector192_21 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 18 then
    if j.val ≤ 5 then
      32
    else
      if j.val ≤ 13 then
        31
      else
        30
  else
    if j.val ≤ 28 then
      if j.val ≤ 21 then
        35
      else
        29
    else
      if j.val ≤ 30 then
        37
      else
        36

def coreSelector192_22 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 17 then
    if j.val ≤ 3 then
      32
    else
      if j.val ≤ 11 then
        31
      else
        30
  else
    if j.val ≤ 27 then
      if j.val ≤ 19 then
        35
      else
        29
    else
      if j.val ≤ 28 then
        28
      else
        36

def coreSelector192_23 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 16 then
    if j.val ≤ 1 then
      32
    else
      if j.val ≤ 9 then
        31
      else
        30
  else
    if j.val ≤ 25 then
      if j.val ≤ 17 then
        35
      else
        29
    else
      if j.val ≤ 27 then
        28
      else
        36

def coreSelector192_24 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      31
    else
      30
  else
    if j.val ≤ 23 then
      29
    else
      if j.val ≤ 26 then
        28
      else
        36

def coreSelector192_25 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 21 then
    if j.val ≤ 5 then
      31
    else
      if j.val ≤ 13 then
        30
      else
        29
  else
    if j.val ≤ 25 then
      28
    else
      if j.val ≤ 26 then
        27
      else
        36

def coreSelector192_26 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 3 then
      31
    else
      if j.val ≤ 11 then
        30
      else
        29
  else
    if j.val ≤ 23 then
      28
    else
      if j.val ≤ 25 then
        27
      else
        36

def coreSelector192_27 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 17 then
    if j.val ≤ 1 then
      31
    else
      if j.val ≤ 9 then
        30
      else
        29
  else
    if j.val ≤ 24 then
      if j.val ≤ 21 then
        28
      else
        27
    else
      if j.val ≤ 30 then
        36
      else
        41

def coreSelector192_28 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 7 then
      30
    else
      if j.val ≤ 15 then
        29
      else
        28
  else
    if j.val ≤ 24 then
      if j.val ≤ 23 then
        27
      else
        26
    else
      if j.val ≤ 29 then
        36
      else
        41

def coreSelector192_29 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 17 then
    if j.val ≤ 5 then
      30
    else
      if j.val ≤ 13 then
        29
      else
        28
  else
    if j.val ≤ 23 then
      if j.val ≤ 21 then
        27
      else
        26
    else
      if j.val ≤ 28 then
        36
      else
        41

def coreSelector192_30 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 11 then
      if j.val ≤ 3 then
        30
      else
        29
    else
      if j.val ≤ 15 then
        28
      else
        27
  else
    if j.val ≤ 23 then
      if j.val ≤ 22 then
        26
      else
        36
    else
      if j.val ≤ 24 then
        25
      else
        if j.val ≤ 27 then
          36
        else
          41

def coreSelector192_31 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 17 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        30
      else
        29
    else
      if j.val ≤ 13 then
        28
      else
        27
  else
    if j.val ≤ 23 then
      if j.val ≤ 21 then
        26
      else
        25
    else
      if j.val ≤ 26 then
        36
      else
        41

def coreSelector192_32 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 11 then
      if j.val ≤ 7 then
        29
      else
        28
    else
      if j.val ≤ 15 then
        27
      else
        26
  else
    if j.val ≤ 25 then
      if j.val ≤ 22 then
        25
      else
        36
    else
      if j.val ≤ 30 then
        41
      else
        40

def coreSelector192_33 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 21 then
    if j.val ≤ 9 then
      if j.val ≤ 5 then
        29
      else
        28
    else
      if j.val ≤ 13 then
        27
      else
        if j.val ≤ 17 then
          26
        else
          25
  else
    if j.val ≤ 24 then
      if j.val ≤ 22 then
        24
      else
        36
    else
      if j.val ≤ 28 then
        41
      else
        if j.val ≤ 30 then
          40
        else
          39

def coreSelector192_34 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        29
      else
        28
    else
      if j.val ≤ 11 then
        27
      else
        if j.val ≤ 15 then
          26
        else
          25
  else
    if j.val ≤ 23 then
      if j.val ≤ 21 then
        24
      else
        36
    else
      if j.val ≤ 26 then
        41
      else
        if j.val ≤ 28 then
          40
        else
          39

def coreSelector192_35 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 17 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        29
      else
        28
    else
      if j.val ≤ 9 then
        27
      else
        if j.val ≤ 13 then
          26
        else
          25
  else
    if j.val ≤ 24 then
      if j.val ≤ 20 then
        24
      else
        if j.val ≤ 22 then
          36
        else
          41
    else
      if j.val ≤ 26 then
        40
      else
        if j.val ≤ 30 then
          39
        else
          38

def coreSelector192_36 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        28
      else
        27
    else
      if j.val ≤ 11 then
        26
      else
        if j.val ≤ 15 then
          25
        else
          24
  else
    if j.val ≤ 24 then
      if j.val ≤ 21 then
        36
      else
        if j.val ≤ 22 then
          41
        else
          40
    else
      if j.val ≤ 27 then
        39
      else
        if j.val ≤ 29 then
          5
        else
          4

def coreSelector192_37 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        28
      else
        if j.val ≤ 5 then
          27
        else
          26
    else
      if j.val ≤ 13 then
        25
      else
        if j.val ≤ 18 then
          24
        else
          36
  else
    if j.val ≤ 25 then
      if j.val ≤ 20 then
        23
      else
        if j.val ≤ 22 then
          40
        else
          39
    else
      if j.val ≤ 27 then
        5
      else
        if j.val ≤ 29 then
          4
        else
          18

def coreSelector192_38 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 20 then
    if j.val ≤ 11 then
      if j.val ≤ 3 then
        27
      else
        if j.val ≤ 7 then
          26
        else
          25
    else
      if j.val ≤ 17 then
        24
      else
        if j.val ≤ 19 then
          23
        else
          22
  else
    if j.val ≤ 24 then
      if j.val ≤ 21 then
        7
      else
        if j.val ≤ 23 then
          6
        else
          20
    else
      if j.val ≤ 27 then
        if j.val ≤ 25 then
          5
        else
          4
      else
        if j.val ≤ 30 then
          18
        else
          3

def coreSelector192_39 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 19 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        27
      else
        if j.val ≤ 5 then
          26
        else
          25
    else
      if j.val ≤ 15 then
        24
      else
        if j.val ≤ 17 then
          23
        else
          22
  else
    if j.val ≤ 23 then
      if j.val ≤ 20 then
        21
      else
        if j.val ≤ 21 then
          6
        else
          20
    else
      if j.val ≤ 25 then
        if j.val ≤ 24 then
          19
        else
          4
      else
        if j.val ≤ 29 then
          18
        else
          17

def coreSelector192_40 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 17 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        26
      else
        25
    else
      if j.val ≤ 13 then
        24
      else
        if j.val ≤ 15 then
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
      if j.val ≤ 23 then
        19
      else
        if j.val ≤ 27 then
          18
        else
          17

def coreSelector192_41 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 15 then
    if j.val ≤ 5 then
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
    if j.val ≤ 21 then
      if j.val ≤ 17 then
        21
      else
        if j.val ≤ 19 then
          20
        else
          19
    else
      if j.val ≤ 25 then
        18
      else
        if j.val ≤ 29 then
          17
        else
          16

def coreSelector192_42 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 15 then
    if j.val ≤ 9 then
      if j.val ≤ 3 then
        25
      else
        24
    else
      if j.val ≤ 11 then
        23
      else
        if j.val ≤ 13 then
          22
        else
          21
  else
    if j.val ≤ 19 then
      if j.val ≤ 17 then
        20
      else
        19
    else
      if j.val ≤ 23 then
        18
      else
        if j.val ≤ 27 then
          17
        else
          16

def coreSelector192_43 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 1 then
        25
      else
        24
    else
      if j.val ≤ 9 then
        23
      else
        if j.val ≤ 11 then
          22
        else
          21
  else
    if j.val ≤ 21 then
      if j.val ≤ 15 then
        20
      else
        if j.val ≤ 17 then
          19
        else
          18
    else
      if j.val ≤ 25 then
        17
      else
        if j.val ≤ 29 then
          16
        else
          15

def coreSelector192_44 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 5 then
        24
      else
        23
    else
      if j.val ≤ 9 then
        22
      else
        if j.val ≤ 11 then
          21
        else
          20
  else
    if j.val ≤ 23 then
      if j.val ≤ 15 then
        19
      else
        if j.val ≤ 19 then
          18
        else
          17
    else
      if j.val ≤ 27 then
        16
      else
        if j.val ≤ 29 then
          15
        else
          14

def coreSelector192_45 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        24
      else
        if j.val ≤ 5 then
          23
        else
          22
    else
      if j.val ≤ 9 then
        21
      else
        if j.val ≤ 11 then
          20
        else
          19
  else
    if j.val ≤ 25 then
      if j.val ≤ 17 then
        18
      else
        if j.val ≤ 21 then
          17
        else
          16
    else
      if j.val ≤ 27 then
        15
      else
        if j.val ≤ 29 then
          14
        else
          13

def coreSelector192_46 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        24
      else
        if j.val ≤ 3 then
          23
        else
          22
    else
      if j.val ≤ 7 then
        21
      else
        if j.val ≤ 9 then
          20
        else
          19
  else
    if j.val ≤ 23 then
      if j.val ≤ 15 then
        18
      else
        if j.val ≤ 19 then
          17
        else
          16
    else
      if j.val ≤ 27 then
        if j.val ≤ 25 then
          15
        else
          14
      else
        if j.val ≤ 29 then
          13
        else
          12

def coreSelector192_47 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        23
      else
        if j.val ≤ 3 then
          22
        else
          21
    else
      if j.val ≤ 7 then
        20
      else
        if j.val ≤ 9 then
          19
        else
          18
  else
    if j.val ≤ 23 then
      if j.val ≤ 17 then
        17
      else
        if j.val ≤ 21 then
          16
        else
          15
    else
      if j.val ≤ 27 then
        if j.val ≤ 25 then
          14
        else
          13
      else
        if j.val ≤ 29 then
          12
        else
          11

def coreSelector192_48 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 15 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        22
      else
        if j.val ≤ 3 then
          21
        else
          20
    else
      if j.val ≤ 7 then
        19
      else
        if j.val ≤ 11 then
          18
        else
          17
  else
    if j.val ≤ 23 then
      if j.val ≤ 19 then
        16
      else
        if j.val ≤ 21 then
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

def coreSelector192_49 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        21
      else
        20
    else
      if j.val ≤ 5 then
        19
      else
        if j.val ≤ 9 then
          18
        else
          17
  else
    if j.val ≤ 21 then
      if j.val ≤ 17 then
        16
      else
        if j.val ≤ 19 then
          15
        else
          14
    else
      if j.val ≤ 23 then
        13
      else
        if j.val ≤ 25 then
          12
        else
          11

def coreSelector192_50 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 15 then
    if j.val ≤ 3 then
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
    if j.val ≤ 21 then
      if j.val ≤ 17 then
        15
      else
        if j.val ≤ 19 then
          14
        else
          13
    else
      if j.val ≤ 23 then
        12
      else
        if j.val ≤ 29 then
          11
        else
          10

def coreSelector192_51 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 15 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        19
      else
        18
    else
      if j.val ≤ 9 then
        17
      else
        if j.val ≤ 13 then
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
      if j.val ≤ 27 then
        11
      else
        if j.val ≤ 29 then
          10
        else
          9

def coreSelector192_52 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        18
      else
        17
    else
      if j.val ≤ 11 then
        16
      else
        if j.val ≤ 13 then
          15
        else
          14
  else
    if j.val ≤ 19 then
      if j.val ≤ 17 then
        13
      else
        12
    else
      if j.val ≤ 25 then
        11
      else
        if j.val ≤ 27 then
          10
        else
          9

def coreSelector192_53 (j : Fin 32) : Fin 42 :=
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
      if j.val ≤ 23 then
        11
      else
        if j.val ≤ 25 then
          10
        else
          9

def coreSelector192_54 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        17
      else
        16
    else
      if j.val ≤ 9 then
        15
      else
        if j.val ≤ 11 then
          14
        else
          13
  else
    if j.val ≤ 21 then
      if j.val ≤ 15 then
        12
      else
        11
    else
      if j.val ≤ 23 then
        10
      else
        if j.val ≤ 30 then
          9
        else
          2

def coreSelector192_55 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        17
      else
        16
    else
      if j.val ≤ 7 then
        15
      else
        if j.val ≤ 9 then
          14
        else
          13
  else
    if j.val ≤ 19 then
      if j.val ≤ 13 then
        12
      else
        11
    else
      if j.val ≤ 21 then
        10
      else
        if j.val ≤ 29 then
          9
        else
          2

def coreSelector192_56 (j : Fin 32) : Fin 42 :=
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
    if j.val ≤ 17 then
      if j.val ≤ 11 then
        12
      else
        11
    else
      if j.val ≤ 19 then
        10
      else
        if j.val ≤ 28 then
          9
        else
          2

def coreSelector192_57 (j : Fin 32) : Fin 42 :=
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
    if j.val ≤ 15 then
      if j.val ≤ 9 then
        12
      else
        11
    else
      if j.val ≤ 17 then
        10
      else
        if j.val ≤ 27 then
          9
        else
          2

def coreSelector192_58 (j : Fin 32) : Fin 42 :=
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
    if j.val ≤ 15 then
      if j.val ≤ 13 then
        11
      else
        10
    else
      if j.val ≤ 26 then
        9
      else
        2

def coreSelector192_59 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 11 then
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
    if j.val ≤ 25 then
      if j.val ≤ 13 then
        10
      else
        9
    else
      if j.val ≤ 29 then
        2
      else
        1

def coreSelector192_60 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        13
      else
        12
    else
      if j.val ≤ 9 then
        11
      else
        10
  else
    if j.val ≤ 27 then
      if j.val ≤ 24 then
        9
      else
        2
    else
      if j.val ≤ 29 then
        1
      else
        0

def coreSelector192_61 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      12
    else
      if j.val ≤ 7 then
        11
      else
        10
  else
    if j.val ≤ 25 then
      if j.val ≤ 23 then
        9
      else
        2
    else
      if j.val ≤ 27 then
        1
      else
        0

def coreSelector192_62 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 22 then
    if j.val ≤ 5 then
      11
    else
      if j.val ≤ 7 then
        10
      else
        9
  else
    if j.val ≤ 23 then
      2
    else
      if j.val ≤ 25 then
        1
      else
        0

def coreSelector192_63 (j : Fin 32) : Fin 42 :=
  if j.val ≤ 21 then
    if j.val ≤ 3 then
      11
    else
      if j.val ≤ 5 then
        10
      else
        9
  else
    if j.val ≤ 22 then
      8
    else
      if j.val ≤ 23 then
        1
      else
        0

def coreSelector192 (b : Fin 64) (j : Fin 32) : Fin 42 :=
  if b.val ≤ 31 then
    if b.val ≤ 15 then
      if b.val ≤ 7 then
        if b.val ≤ 3 then
          if b.val ≤ 1 then
            if b.val ≤ 0 then
              coreSelector192_0 j
            else
              coreSelector192_1 j
          else
            if b.val ≤ 2 then
              coreSelector192_2 j
            else
              coreSelector192_3 j
        else
          if b.val ≤ 5 then
            if b.val ≤ 4 then
              coreSelector192_4 j
            else
              coreSelector192_5 j
          else
            if b.val ≤ 6 then
              coreSelector192_6 j
            else
              coreSelector192_7 j
      else
        if b.val ≤ 11 then
          if b.val ≤ 9 then
            if b.val ≤ 8 then
              coreSelector192_8 j
            else
              coreSelector192_9 j
          else
            if b.val ≤ 10 then
              coreSelector192_10 j
            else
              coreSelector192_11 j
        else
          if b.val ≤ 13 then
            if b.val ≤ 12 then
              coreSelector192_12 j
            else
              coreSelector192_13 j
          else
            if b.val ≤ 14 then
              coreSelector192_14 j
            else
              coreSelector192_15 j
    else
      if b.val ≤ 23 then
        if b.val ≤ 19 then
          if b.val ≤ 17 then
            if b.val ≤ 16 then
              coreSelector192_16 j
            else
              coreSelector192_17 j
          else
            if b.val ≤ 18 then
              coreSelector192_18 j
            else
              coreSelector192_19 j
        else
          if b.val ≤ 21 then
            if b.val ≤ 20 then
              coreSelector192_20 j
            else
              coreSelector192_21 j
          else
            if b.val ≤ 22 then
              coreSelector192_22 j
            else
              coreSelector192_23 j
      else
        if b.val ≤ 27 then
          if b.val ≤ 25 then
            if b.val ≤ 24 then
              coreSelector192_24 j
            else
              coreSelector192_25 j
          else
            if b.val ≤ 26 then
              coreSelector192_26 j
            else
              coreSelector192_27 j
        else
          if b.val ≤ 29 then
            if b.val ≤ 28 then
              coreSelector192_28 j
            else
              coreSelector192_29 j
          else
            if b.val ≤ 30 then
              coreSelector192_30 j
            else
              coreSelector192_31 j
  else
    if b.val ≤ 47 then
      if b.val ≤ 39 then
        if b.val ≤ 35 then
          if b.val ≤ 33 then
            if b.val ≤ 32 then
              coreSelector192_32 j
            else
              coreSelector192_33 j
          else
            if b.val ≤ 34 then
              coreSelector192_34 j
            else
              coreSelector192_35 j
        else
          if b.val ≤ 37 then
            if b.val ≤ 36 then
              coreSelector192_36 j
            else
              coreSelector192_37 j
          else
            if b.val ≤ 38 then
              coreSelector192_38 j
            else
              coreSelector192_39 j
      else
        if b.val ≤ 43 then
          if b.val ≤ 41 then
            if b.val ≤ 40 then
              coreSelector192_40 j
            else
              coreSelector192_41 j
          else
            if b.val ≤ 42 then
              coreSelector192_42 j
            else
              coreSelector192_43 j
        else
          if b.val ≤ 45 then
            if b.val ≤ 44 then
              coreSelector192_44 j
            else
              coreSelector192_45 j
          else
            if b.val ≤ 46 then
              coreSelector192_46 j
            else
              coreSelector192_47 j
    else
      if b.val ≤ 55 then
        if b.val ≤ 51 then
          if b.val ≤ 49 then
            if b.val ≤ 48 then
              coreSelector192_48 j
            else
              coreSelector192_49 j
          else
            if b.val ≤ 50 then
              coreSelector192_50 j
            else
              coreSelector192_51 j
        else
          if b.val ≤ 53 then
            if b.val ≤ 52 then
              coreSelector192_52 j
            else
              coreSelector192_53 j
          else
            if b.val ≤ 54 then
              coreSelector192_54 j
            else
              coreSelector192_55 j
      else
        if b.val ≤ 59 then
          if b.val ≤ 57 then
            if b.val ≤ 56 then
              coreSelector192_56 j
            else
              coreSelector192_57 j
          else
            if b.val ≤ 58 then
              coreSelector192_58 j
            else
              coreSelector192_59 j
        else
          if b.val ≤ 61 then
            if b.val ≤ 60 then
              coreSelector192_60 j
            else
              coreSelector192_61 j
          else
            if b.val ≤ 62 then
              coreSelector192_62 j
            else
              coreSelector192_63 j
def coreMetadataChunks192 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨185, [5, 37], [0, 0, 1, 2, 4]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩, ⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨175, [5, 5, 7], [0, 0, 1, 3, 6]⟩]
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨183, [3, 61], [0, 1, 2, 4, 8]⟩, ⟨177, [3, 59], [0, 1, 2, 4, 8]⟩, ⟨159, [3, 53], [0, 1, 2, 4, 8]⟩, ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩, ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨171, [3, 3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨153, [3, 3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨147, [3, 7, 7], [0, 1, 2, 5, 10]⟩, ⟨189, [3, 3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨135, [3, 3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨165, [3, 5, 11], [0, 1, 3, 6, 13]⟩, ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]
end Erdos883Verified
