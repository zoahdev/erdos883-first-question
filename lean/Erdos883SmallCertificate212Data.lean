import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData212 : List CoreOddData :=
  [⟨1, [], [0, 0, 0, 0, 0]⟩,
   ⟨211, [211], [0, 0, 0, 0, 0]⟩,
   ⟨199, [199], [0, 0, 0, 0, 0]⟩,
   ⟨197, [197], [0, 0, 0, 0, 0]⟩,
   ⟨193, [193], [0, 0, 0, 0, 0]⟩,
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
   ⟨209, [11, 19], [0, 0, 0, 0, 1]⟩,
   ⟨7, [7], [0, 0, 0, 1, 2]⟩,
   ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩,
   ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩,
   ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩,
   ⟨203, [7, 29], [0, 0, 0, 1, 2]⟩,
   ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩,
   ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩,
   ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩,
   ⟨5, [5], [0, 0, 1, 2, 4]⟩,
   ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩,
   ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩,
   ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩,
   ⟨205, [5, 41], [0, 0, 1, 2, 4]⟩,
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
   ⟨201, [3, 67], [0, 1, 2, 4, 8]⟩,
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
   ⟨207, [3, 3, 23], [0, 1, 2, 4, 8]⟩,
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
   ⟨195, [3, 5, 13], [0, 1, 3, 6, 12]⟩,
   ⟨165, [3, 5, 11], [0, 1, 3, 6, 13]⟩,
   ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreResources212 (i : Fin 46) : CoreResourceData :=
  if i.val ≤ 22 then
    if i.val ≤ 10 then
      if i.val ≤ 4 then
        if i.val ≤ 1 then
          if i.val ≤ 0 then
            ⟨24, 0, 191, false⟩
          else
            ⟨25, 0, 190, false⟩
        else
          if i.val ≤ 2 then
            ⟨29, 0, 189, false⟩
          else
            if i.val ≤ 3 then
              ⟨47, 0, 153, false⟩
            else
              ⟨50, 0, 142, false⟩
      else
        if i.val ≤ 7 then
          if i.val ≤ 5 then
            ⟨51, 0, 140, false⟩
          else
            if i.val ≤ 6 then
              ⟨52, 0, 134, false⟩
            else
              ⟨53, 0, 133, false⟩
        else
          if i.val ≤ 8 then
            ⟨24, 0, 96, true⟩
          else
            if i.val ≤ 9 then
              ⟨25, 0, 95, true⟩
            else
              ⟨33, 0, 94, true⟩
    else
      if i.val ≤ 16 then
        if i.val ≤ 13 then
          if i.val ≤ 11 then
            ⟨34, 0, 93, true⟩
          else
            if i.val ≤ 12 then
              ⟨37, 0, 92, true⟩
            else
              ⟨38, 0, 91, true⟩
        else
          if i.val ≤ 14 then
            ⟨39, 0, 90, true⟩
          else
            if i.val ≤ 15 then
              ⟨40, 0, 89, true⟩
            else
              ⟨41, 0, 87, true⟩
      else
        if i.val ≤ 19 then
          if i.val ≤ 17 then
            ⟨42, 0, 86, true⟩
          else
            if i.val ≤ 18 then
              ⟨44, 0, 84, true⟩
            else
              ⟨46, 0, 81, true⟩
        else
          if i.val ≤ 20 then
            ⟨47, 0, 76, true⟩
          else
            if i.val ≤ 21 then
              ⟨50, 0, 71, true⟩
            else
              ⟨51, 0, 70, true⟩
  else
    if i.val ≤ 33 then
      if i.val ≤ 27 then
        if i.val ≤ 24 then
          if i.val ≤ 23 then
            ⟨52, 0, 67, true⟩
          else
            ⟨53, 0, 66, true⟩
        else
          if i.val ≤ 25 then
            ⟨55, 0, 65, true⟩
          else
            if i.val ≤ 26 then
              ⟨58, 0, 62, true⟩
            else
              ⟨59, 0, 61, true⟩
      else
        if i.val ≤ 30 then
          if i.val ≤ 28 then
            ⟨60, 0, 59, true⟩
          else
            if i.val ≤ 29 then
              ⟨62, 0, 58, true⟩
            else
              ⟨64, 0, 57, true⟩
        else
          if i.val ≤ 31 then
            ⟨67, 0, 56, true⟩
          else
            if i.val ≤ 32 then
              ⟨71, 0, 55, true⟩
            else
              ⟨75, 0, 44, true⟩
    else
      if i.val ≤ 39 then
        if i.val ≤ 36 then
          if i.val ≤ 34 then
            ⟨79, 0, 43, true⟩
          else
            if i.val ≤ 35 then
              ⟨85, 0, 42, true⟩
            else
              ⟨93, 0, 41, true⟩
        else
          if i.val ≤ 37 then
            ⟨103, 0, 40, true⟩
          else
            if i.val ≤ 38 then
              ⟨106, 0, 37, true⟩
            else
              ⟨83, 1, 55, true⟩
      else
        if i.val ≤ 42 then
          if i.val ≤ 40 then
            ⟨68, 2, 65, true⟩
          else
            if i.val ≤ 41 then
              ⟨69, 2, 64, true⟩
            else
              ⟨71, 2, 60, true⟩
        else
          if i.val ≤ 43 then
            ⟨58, 3, 73, true⟩
          else
            if i.val ≤ 44 then
              ⟨60, 3, 72, true⟩
            else
              ⟨63, 3, 70, true⟩

def coreChunks212_0 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨211, [211], [0, 0, 0, 0, 0]⟩, ⟨199, [199], [0, 0, 0, 0, 0]⟩, ⟨197, [197], [0, 0, 0, 0, 0]⟩, ⟨193, [193], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩]

def coreChunks212_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨89, [89], [0, 0, 0, 0, 0]⟩]

def coreChunks212_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩]

def coreChunks212_3 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩]
  | _ => [⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨209, [11, 19], [0, 0, 0, 0, 1]⟩]

def coreChunks212_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩]

def coreChunks212_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨143, [11, 13], [0, 0, 0, 0, 1]⟩]

def coreChunks212_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨203, [7, 29], [0, 0, 0, 1, 2]⟩]

def coreChunks212_7 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨161, [7, 23], [0, 0, 0, 1, 2]⟩]

def coreChunks212_8 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨211, [211], [0, 0, 0, 0, 0]⟩, ⟨199, [199], [0, 0, 0, 0, 0]⟩, ⟨197, [197], [0, 0, 0, 0, 0]⟩, ⟨193, [193], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩]
  | _ => [⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩]

def coreChunks212_9 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨89, [89], [0, 0, 0, 0, 0]⟩]

def coreChunks212_10 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩]

def coreChunks212_11 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨47, [47], [0, 0, 0, 0, 0]⟩]

def coreChunks212_12 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩]

def coreChunks212_13 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨31, [31], [0, 0, 0, 0, 0]⟩]

def coreChunks212_14 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨29, [29], [0, 0, 0, 0, 0]⟩]

def coreChunks212_15 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks212_16 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨19, [19], [0, 0, 0, 0, 0]⟩]

def coreChunks212_17 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks212_18 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩]

def coreChunks212_19 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩]

def coreChunks212_20 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨209, [11, 19], [0, 0, 0, 0, 1]⟩]

def coreChunks212_21 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩]

def coreChunks212_22 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨143, [11, 13], [0, 0, 0, 0, 1]⟩]

def coreChunks212_23 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨203, [7, 29], [0, 0, 0, 1, 2]⟩]

def coreChunks212_24 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨161, [7, 23], [0, 0, 0, 1, 2]⟩]

def coreChunks212_25 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩]

def coreChunks212_26 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks212_27 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩]

def coreChunks212_28 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨205, [5, 41], [0, 0, 1, 2, 4]⟩]

def coreChunks212_29 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨185, [5, 37], [0, 0, 1, 2, 4]⟩]

def coreChunks212_30 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩]

def coreChunks212_31 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩]

def coreChunks212_32 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨175, [5, 5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks212_33 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks212_34 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨201, [3, 67], [0, 1, 2, 4, 8]⟩, ⟨183, [3, 61], [0, 1, 2, 4, 8]⟩, ⟨177, [3, 59], [0, 1, 2, 4, 8]⟩, ⟨159, [3, 53], [0, 1, 2, 4, 8]⟩]

def coreChunks212_35 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨141, [3, 47], [0, 1, 2, 4, 8]⟩, ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩]

def coreChunks212_36 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨207, [3, 3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨171, [3, 3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨153, [3, 3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩]

def coreChunks212_37 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨147, [3, 7, 7], [0, 1, 2, 5, 10]⟩, ⟨189, [3, 3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨135, [3, 3, 3, 5], [0, 1, 3, 6, 12]⟩]

def coreChunks212_38 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨195, [3, 5, 13], [0, 1, 3, 6, 12]⟩, ⟨165, [3, 5, 11], [0, 1, 3, 6, 13]⟩, ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]

def coreChunks212_39 (c : Fin 6) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨211, [211], [0, 0, 0, 0, 0]⟩, ⟨199, [199], [0, 0, 0, 0, 0]⟩, ⟨197, [197], [0, 0, 0, 0, 0]⟩, ⟨193, [193], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨209, [11, 19], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩]
  | 3 => [⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨203, [7, 29], [0, 0, 0, 1, 2]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨205, [5, 41], [0, 0, 1, 2, 4]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨185, [5, 37], [0, 0, 1, 2, 4]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩]
  | 4 => [⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨175, [5, 5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨201, [3, 67], [0, 1, 2, 4, 8]⟩, ⟨183, [3, 61], [0, 1, 2, 4, 8]⟩, ⟨177, [3, 59], [0, 1, 2, 4, 8]⟩, ⟨159, [3, 53], [0, 1, 2, 4, 8]⟩, ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩]
  | _ => [⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩]

def coreChunks212_40 (c : Fin 5) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨211, [211], [0, 0, 0, 0, 0]⟩, ⟨199, [199], [0, 0, 0, 0, 0]⟩, ⟨197, [197], [0, 0, 0, 0, 0]⟩, ⟨193, [193], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨209, [11, 19], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩]
  | 3 => [⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨203, [7, 29], [0, 0, 0, 1, 2]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨205, [5, 41], [0, 0, 1, 2, 4]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨185, [5, 37], [0, 0, 1, 2, 4]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩]
  | _ => [⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩]

def coreChunks212_41 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨55, [5, 11], [0, 0, 1, 2, 5]⟩]

def coreChunks212_42 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨175, [5, 5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks212_43 (c : Fin 4) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨211, [211], [0, 0, 0, 0, 0]⟩, ⟨199, [199], [0, 0, 0, 0, 0]⟩, ⟨197, [197], [0, 0, 0, 0, 0]⟩, ⟨193, [193], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩]
  | 1 => [⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩]
  | 2 => [⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨209, [11, 19], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩]
  | _ => [⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨203, [7, 29], [0, 0, 0, 1, 2]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks212_44 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨205, [5, 41], [0, 0, 1, 2, 4]⟩]

def coreChunks212_45 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨185, [5, 37], [0, 0, 1, 2, 4]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩]

def coreSelector212_0 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 5 then
    38
  else
    if j.val ≤ 25 then
      37
    else
      36

def coreSelector212_1 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 3 then
    38
  else
    if j.val ≤ 23 then
      37
    else
      36

def coreSelector212_2 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 1 then
    38
  else
    if j.val ≤ 21 then
      37
    else
      36

def coreSelector212_3 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    37
  else
    36

def coreSelector212_4 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    37
  else
    if j.val ≤ 33 then
      36
    else
      35

def coreSelector212_5 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 15 then
    37
  else
    if j.val ≤ 31 then
      36
    else
      35

def coreSelector212_6 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 13 then
    37
  else
    if j.val ≤ 29 then
      36
    else
      35

def coreSelector212_7 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 11 then
    37
  else
    if j.val ≤ 27 then
      36
    else
      35

def coreSelector212_8 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 25 then
    if j.val ≤ 9 then
      37
    else
      36
  else
    if j.val ≤ 33 then
      35
    else
      39

def coreSelector212_9 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 23 then
    if j.val ≤ 7 then
      37
    else
      36
  else
    if j.val ≤ 32 then
      35
    else
      39

def coreSelector212_10 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 5 then
      37
    else
      36
  else
    if j.val ≤ 31 then
      35
    else
      39

def coreSelector212_11 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 3 then
      37
    else
      36
  else
    if j.val ≤ 30 then
      35
    else
      39

def coreSelector212_12 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 1 then
      37
    else
      36
  else
    if j.val ≤ 29 then
      35
    else
      if j.val ≤ 30 then
        34
      else
        39

def coreSelector212_13 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 27 then
    if j.val ≤ 15 then
      36
    else
      35
  else
    if j.val ≤ 29 then
      34
    else
      39

def coreSelector212_14 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 25 then
    if j.val ≤ 13 then
      36
    else
      35
  else
    if j.val ≤ 28 then
      34
    else
      39

def coreSelector212_15 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 23 then
    if j.val ≤ 11 then
      36
    else
      35
  else
    if j.val ≤ 27 then
      34
    else
      39

def coreSelector212_16 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 9 then
      36
    else
      35
  else
    if j.val ≤ 26 then
      34
    else
      39

def coreSelector212_17 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 7 then
      36
    else
      35
  else
    if j.val ≤ 25 then
      34
    else
      39

def coreSelector212_18 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 5 then
      36
    else
      35
  else
    if j.val ≤ 24 then
      34
    else
      if j.val ≤ 33 then
        39
      else
        32

def coreSelector212_19 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 23 then
    if j.val ≤ 3 then
      36
    else
      if j.val ≤ 15 then
        35
      else
        34
  else
    if j.val ≤ 24 then
      33
    else
      if j.val ≤ 31 then
        39
      else
        32

def coreSelector212_20 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 1 then
      36
    else
      if j.val ≤ 13 then
        35
      else
        34
  else
    if j.val ≤ 23 then
      33
    else
      if j.val ≤ 29 then
        39
      else
        32

def coreSelector212_21 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 22 then
    if j.val ≤ 11 then
      35
    else
      if j.val ≤ 19 then
        34
      else
        33
  else
    if j.val ≤ 27 then
      39
    else
      if j.val ≤ 33 then
        32
      else
        42

def coreSelector212_22 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 9 then
      35
    else
      if j.val ≤ 17 then
        34
      else
        33
  else
    if j.val ≤ 25 then
      39
    else
      if j.val ≤ 32 then
        32
      else
        42

def coreSelector212_23 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 20 then
    if j.val ≤ 7 then
      35
    else
      if j.val ≤ 15 then
        34
      else
        33
  else
    if j.val ≤ 31 then
      if j.val ≤ 23 then
        39
      else
        32
    else
      if j.val ≤ 32 then
        31
      else
        41

def coreSelector212_24 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 13 then
      if j.val ≤ 5 then
        35
      else
        34
    else
      if j.val ≤ 19 then
        33
      else
        39
  else
    if j.val ≤ 31 then
      if j.val ≤ 29 then
        32
      else
        31
    else
      if j.val ≤ 32 then
        41
      else
        40

def coreSelector212_25 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 18 then
    if j.val ≤ 3 then
      35
    else
      if j.val ≤ 11 then
        34
      else
        33
  else
    if j.val ≤ 27 then
      if j.val ≤ 19 then
        39
      else
        32
    else
      if j.val ≤ 30 then
        31
      else
        40

def coreSelector212_26 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 1 then
      35
    else
      if j.val ≤ 9 then
        34
      else
        33
  else
    if j.val ≤ 25 then
      32
    else
      if j.val ≤ 29 then
        31
      else
        40

def coreSelector212_27 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      34
    else
      33
  else
    if j.val ≤ 23 then
      32
    else
      if j.val ≤ 28 then
        31
      else
        40

def coreSelector212_28 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 5 then
      34
    else
      if j.val ≤ 13 then
        33
      else
        32
  else
    if j.val ≤ 27 then
      31
    else
      if j.val ≤ 28 then
        30
      else
        40

def coreSelector212_29 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 3 then
      34
    else
      if j.val ≤ 11 then
        33
      else
        32
  else
    if j.val ≤ 25 then
      31
    else
      if j.val ≤ 27 then
        30
      else
        40

def coreSelector212_30 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 1 then
      34
    else
      if j.val ≤ 9 then
        33
      else
        32
  else
    if j.val ≤ 23 then
      31
    else
      if j.val ≤ 26 then
        30
      else
        40

def coreSelector212_31 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 7 then
      33
    else
      if j.val ≤ 15 then
        32
      else
        31
  else
    if j.val ≤ 26 then
      if j.val ≤ 25 then
        30
      else
        29
    else
      if j.val ≤ 33 then
        40
      else
        45

def coreSelector212_32 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 5 then
      33
    else
      if j.val ≤ 13 then
        32
      else
        31
  else
    if j.val ≤ 25 then
      if j.val ≤ 23 then
        30
      else
        29
    else
      if j.val ≤ 32 then
        40
      else
        45

def coreSelector212_33 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 3 then
      33
    else
      if j.val ≤ 11 then
        32
      else
        31
  else
    if j.val ≤ 24 then
      if j.val ≤ 21 then
        30
      else
        29
    else
      if j.val ≤ 31 then
        40
      else
        45

def coreSelector212_34 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 23 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        33
      else
        32
    else
      if j.val ≤ 15 then
        31
      else
        if j.val ≤ 19 then
          30
        else
          29
  else
    if j.val ≤ 26 then
      if j.val ≤ 24 then
        28
      else
        if j.val ≤ 25 then
          40
        else
          27
    else
      if j.val ≤ 30 then
        40
      else
        if j.val ≤ 32 then
          45
        else
          44

def coreSelector212_35 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 23 then
    if j.val ≤ 13 then
      if j.val ≤ 7 then
        32
      else
        31
    else
      if j.val ≤ 17 then
        30
      else
        if j.val ≤ 21 then
          29
        else
          28
  else
    if j.val ≤ 26 then
      if j.val ≤ 25 then
        27
      else
        26
    else
      if j.val ≤ 29 then
        40
      else
        if j.val ≤ 30 then
          45
        else
          44

def coreSelector212_36 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 11 then
      if j.val ≤ 5 then
        32
      else
        31
    else
      if j.val ≤ 15 then
        30
      else
        if j.val ≤ 19 then
          29
        else
          28
  else
    if j.val ≤ 25 then
      if j.val ≤ 23 then
        27
      else
        26
    else
      if j.val ≤ 28 then
        40
      else
        if j.val ≤ 32 then
          44
        else
          43

def coreSelector212_37 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 9 then
      if j.val ≤ 3 then
        32
      else
        31
    else
      if j.val ≤ 13 then
        30
      else
        if j.val ≤ 17 then
          29
        else
          28
  else
    if j.val ≤ 24 then
      if j.val ≤ 21 then
        27
      else
        26
    else
      if j.val ≤ 27 then
        40
      else
        if j.val ≤ 30 then
          44
        else
          43

def coreSelector212_38 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 7 then
      if j.val ≤ 1 then
        32
      else
        31
    else
      if j.val ≤ 11 then
        30
      else
        if j.val ≤ 15 then
          29
        else
          28
  else
    if j.val ≤ 25 then
      if j.val ≤ 19 then
        27
      else
        if j.val ≤ 23 then
          26
        else
          40
    else
      if j.val ≤ 26 then
        25
      else
        if j.val ≤ 28 then
          44
        else
          43

def coreSelector212_39 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 22 then
    if j.val ≤ 13 then
      if j.val ≤ 5 then
        31
      else
        if j.val ≤ 9 then
          30
        else
          29
    else
      if j.val ≤ 15 then
        28
      else
        if j.val ≤ 17 then
          27
        else
          26
  else
    if j.val ≤ 26 then
      if j.val ≤ 23 then
        40
      else
        if j.val ≤ 25 then
          25
        else
          44
    else
      if j.val ≤ 31 then
        43
      else
        if j.val ≤ 33 then
          5
        else
          4

def coreSelector212_40 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 11 then
      if j.val ≤ 3 then
        31
      else
        if j.val ≤ 7 then
          30
        else
          29
    else
      if j.val ≤ 13 then
        28
      else
        if j.val ≤ 15 then
          27
        else
          26
  else
    if j.val ≤ 26 then
      if j.val ≤ 24 then
        25
      else
        if j.val ≤ 25 then
          43
        else
          7
    else
      if j.val ≤ 29 then
        43
      else
        if j.val ≤ 31 then
          5
        else
          4

def coreSelector212_41 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        31
      else
        if j.val ≤ 5 then
          30
        else
          29
    else
      if j.val ≤ 11 then
        28
      else
        if j.val ≤ 13 then
          27
        else
          26
  else
    if j.val ≤ 25 then
      if j.val ≤ 23 then
        25
      else
        if j.val ≤ 24 then
          24
        else
          7
    else
      if j.val ≤ 28 then
        if j.val ≤ 27 then
          6
        else
          22
      else
        if j.val ≤ 29 then
          5
        else
          4

def coreSelector212_42 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 9 then
      if j.val ≤ 3 then
        30
      else
        if j.val ≤ 7 then
          29
        else
          28
    else
      if j.val ≤ 11 then
        27
      else
        if j.val ≤ 17 then
          26
        else
          25
  else
    if j.val ≤ 25 then
      if j.val ≤ 23 then
        24
      else
        if j.val ≤ 24 then
          23
        else
          6
    else
      if j.val ≤ 28 then
        if j.val ≤ 27 then
          22
        else
          21
      else
        if j.val ≤ 33 then
          4
        else
          3

def coreSelector212_43 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 7 then
      if j.val ≤ 1 then
        30
      else
        if j.val ≤ 5 then
          29
        else
          28
    else
      if j.val ≤ 15 then
        if j.val ≤ 9 then
          27
        else
          26
      else
        if j.val ≤ 19 then
          25
        else
          24
  else
    if j.val ≤ 27 then
      if j.val ≤ 23 then
        23
      else
        if j.val ≤ 25 then
          22
        else
          21
    else
      if j.val ≤ 32 then
        if j.val ≤ 31 then
          4
        else
          20
      else
        if j.val ≤ 33 then
          3
        else
          19

def coreSelector212_44 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        29
      else
        if j.val ≤ 5 then
          28
        else
          27
    else
      if j.val ≤ 13 then
        26
      else
        if j.val ≤ 17 then
          25
        else
          24
  else
    if j.val ≤ 26 then
      if j.val ≤ 21 then
        23
      else
        if j.val ≤ 23 then
          22
        else
          21
    else
      if j.val ≤ 29 then
        4
      else
        if j.val ≤ 31 then
          20
        else
          19

def coreSelector212_45 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        29
      else
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
    if j.val ≤ 25 then
      if j.val ≤ 19 then
        23
      else
        if j.val ≤ 21 then
          22
        else
          21
    else
      if j.val ≤ 29 then
        if j.val ≤ 27 then
          4
        else
          20
      else
        if j.val ≤ 33 then
          19
        else
          18

def coreSelector212_46 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        28
      else
        if j.val ≤ 3 then
          27
        else
          26
    else
      if j.val ≤ 13 then
        25
      else
        if j.val ≤ 15 then
          24
        else
          23
  else
    if j.val ≤ 25 then
      if j.val ≤ 19 then
        22
      else
        if j.val ≤ 24 then
          21
        else
          4
    else
      if j.val ≤ 27 then
        20
      else
        if j.val ≤ 31 then
          19
        else
          18

def coreSelector212_47 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      if j.val ≤ 1 then
        27
      else
        26
    else
      if j.val ≤ 11 then
        25
      else
        if j.val ≤ 13 then
          24
        else
          23
  else
    if j.val ≤ 25 then
      if j.val ≤ 17 then
        22
      else
        if j.val ≤ 23 then
          21
        else
          20
    else
      if j.val ≤ 29 then
        19
      else
        if j.val ≤ 33 then
          18
        else
          17

def coreSelector212_48 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 15 then
    if j.val ≤ 9 then
      if j.val ≤ 5 then
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
    if j.val ≤ 27 then
      if j.val ≤ 21 then
        21
      else
        if j.val ≤ 23 then
          20
        else
          19
    else
      if j.val ≤ 31 then
        18
      else
        if j.val ≤ 33 then
          17
        else
          16

def coreSelector212_49 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 9 then
      if j.val ≤ 3 then
        26
      else
        if j.val ≤ 7 then
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
    if j.val ≤ 29 then
      if j.val ≤ 21 then
        20
      else
        if j.val ≤ 25 then
          19
        else
          18
    else
      if j.val ≤ 31 then
        17
      else
        if j.val ≤ 33 then
          16
        else
          15

def coreSelector212_50 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 7 then
      if j.val ≤ 1 then
        26
      else
        if j.val ≤ 5 then
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
    if j.val ≤ 27 then
      if j.val ≤ 19 then
        20
      else
        if j.val ≤ 23 then
          19
        else
          18
    else
      if j.val ≤ 31 then
        if j.val ≤ 29 then
          17
        else
          16
      else
        if j.val ≤ 33 then
          15
        else
          14

def coreSelector212_51 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        25
      else
        if j.val ≤ 5 then
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
          20
  else
    if j.val ≤ 27 then
      if j.val ≤ 21 then
        19
      else
        if j.val ≤ 25 then
          18
        else
          17
    else
      if j.val ≤ 31 then
        if j.val ≤ 29 then
          16
        else
          15
      else
        if j.val ≤ 33 then
          14
        else
          13

def coreSelector212_52 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        25
      else
        if j.val ≤ 3 then
          24
        else
          23
    else
      if j.val ≤ 13 then
        if j.val ≤ 7 then
          22
        else
          21
      else
        if j.val ≤ 15 then
          20
        else
          19
  else
    if j.val ≤ 27 then
      if j.val ≤ 23 then
        18
      else
        if j.val ≤ 25 then
          17
        else
          16
    else
      if j.val ≤ 31 then
        if j.val ≤ 29 then
          15
        else
          14
      else
        if j.val ≤ 33 then
          13
        else
          12

def coreSelector212_53 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        24
      else
        if j.val ≤ 3 then
          23
        else
          22
    else
      if j.val ≤ 11 then
        21
      else
        if j.val ≤ 13 then
          20
        else
          19
  else
    if j.val ≤ 25 then
      if j.val ≤ 21 then
        18
      else
        if j.val ≤ 23 then
          17
        else
          16
    else
      if j.val ≤ 29 then
        if j.val ≤ 27 then
          15
        else
          14
      else
        if j.val ≤ 31 then
          13
        else
          12

def coreSelector212_54 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        23
      else
        if j.val ≤ 3 then
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
    if j.val ≤ 25 then
      if j.val ≤ 21 then
        17
      else
        if j.val ≤ 23 then
          16
        else
          15
    else
      if j.val ≤ 27 then
        14
      else
        if j.val ≤ 29 then
          13
        else
          12

def coreSelector212_55 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 9 then
      if j.val ≤ 1 then
        22
      else
        if j.val ≤ 7 then
          21
        else
          20
    else
      if j.val ≤ 13 then
        19
      else
        if j.val ≤ 17 then
          18
        else
          17
  else
    if j.val ≤ 25 then
      if j.val ≤ 21 then
        16
      else
        if j.val ≤ 23 then
          15
        else
          14
    else
      if j.val ≤ 27 then
        13
      else
        if j.val ≤ 33 then
          12
        else
          11

def coreSelector212_56 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 19 then
    if j.val ≤ 11 then
      if j.val ≤ 5 then
        21
      else
        if j.val ≤ 7 then
          20
        else
          19
    else
      if j.val ≤ 15 then
        18
      else
        if j.val ≤ 17 then
          17
        else
          16
  else
    if j.val ≤ 25 then
      if j.val ≤ 21 then
        15
      else
        if j.val ≤ 23 then
          14
        else
          13
    else
      if j.val ≤ 31 then
        12
      else
        if j.val ≤ 33 then
          11
        else
          10

def coreSelector212_57 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 17 then
    if j.val ≤ 9 then
      if j.val ≤ 3 then
        21
      else
        if j.val ≤ 5 then
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
          16
  else
    if j.val ≤ 23 then
      if j.val ≤ 19 then
        15
      else
        if j.val ≤ 21 then
          14
        else
          13
    else
      if j.val ≤ 29 then
        12
      else
        if j.val ≤ 31 then
          11
        else
          10

def coreSelector212_58 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 15 then
    if j.val ≤ 7 then
      if j.val ≤ 1 then
        21
      else
        if j.val ≤ 3 then
          20
        else
          19
    else
      if j.val ≤ 11 then
        18
      else
        if j.val ≤ 13 then
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
      if j.val ≤ 27 then
        12
      else
        if j.val ≤ 29 then
          11
        else
          10

def coreSelector212_59 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 13 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
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
    if j.val ≤ 19 then
      if j.val ≤ 15 then
        15
      else
        if j.val ≤ 17 then
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

def coreSelector212_60 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 13 then
    if j.val ≤ 7 then
      if j.val ≤ 3 then
        19
      else
        18
    else
      if j.val ≤ 9 then
        17
      else
        if j.val ≤ 11 then
          16
        else
          15
  else
    if j.val ≤ 23 then
      if j.val ≤ 15 then
        14
      else
        if j.val ≤ 17 then
          13
        else
          12
    else
      if j.val ≤ 25 then
        11
      else
        if j.val ≤ 33 then
          10
        else
          2

def coreSelector212_61 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      if j.val ≤ 1 then
        19
      else
        18
    else
      if j.val ≤ 7 then
        17
      else
        if j.val ≤ 9 then
          16
        else
          15
  else
    if j.val ≤ 21 then
      if j.val ≤ 13 then
        14
      else
        if j.val ≤ 15 then
          13
        else
          12
    else
      if j.val ≤ 23 then
        11
      else
        if j.val ≤ 32 then
          10
        else
          2

def coreSelector212_62 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 11 then
    if j.val ≤ 5 then
      if j.val ≤ 3 then
        18
      else
        17
    else
      if j.val ≤ 7 then
        16
      else
        if j.val ≤ 9 then
          15
        else
          14
  else
    if j.val ≤ 19 then
      if j.val ≤ 13 then
        13
      else
        12
    else
      if j.val ≤ 21 then
        11
      else
        if j.val ≤ 31 then
          10
        else
          2

def coreSelector212_63 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        18
      else
        17
    else
      if j.val ≤ 5 then
        16
      else
        if j.val ≤ 7 then
          15
        else
          14
  else
    if j.val ≤ 17 then
      if j.val ≤ 11 then
        13
      else
        12
    else
      if j.val ≤ 19 then
        11
      else
        if j.val ≤ 30 then
          10
        else
          2

def coreSelector212_64 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 9 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        17
      else
        16
    else
      if j.val ≤ 5 then
        15
      else
        if j.val ≤ 7 then
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
      if j.val ≤ 29 then
        10
      else
        if j.val ≤ 33 then
          2
        else
          1

def coreSelector212_65 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 13 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        16
      else
        15
    else
      if j.val ≤ 5 then
        14
      else
        if j.val ≤ 7 then
          13
        else
          12
  else
    if j.val ≤ 28 then
      if j.val ≤ 15 then
        11
      else
        10
    else
      if j.val ≤ 31 then
        2
      else
        if j.val ≤ 33 then
          1
        else
          0

def coreSelector212_66 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 11 then
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
    if j.val ≤ 27 then
      if j.val ≤ 13 then
        11
      else
        10
    else
      if j.val ≤ 29 then
        2
      else
        if j.val ≤ 31 then
          1
        else
          0

def coreSelector212_67 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 11 then
    if j.val ≤ 3 then
      if j.val ≤ 1 then
        14
      else
        13
    else
      if j.val ≤ 9 then
        12
      else
        11
  else
    if j.val ≤ 27 then
      if j.val ≤ 26 then
        10
      else
        2
    else
      if j.val ≤ 29 then
        1
      else
        0

def coreSelector212_68 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 9 then
    if j.val ≤ 1 then
      13
    else
      if j.val ≤ 7 then
        12
      else
        11
  else
    if j.val ≤ 26 then
      if j.val ≤ 25 then
        10
      else
        9
    else
      if j.val ≤ 27 then
        1
      else
        0

def coreSelector212_69 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 23 then
    if j.val ≤ 5 then
      12
    else
      if j.val ≤ 7 then
        11
      else
        10
  else
    if j.val ≤ 25 then
      9
    else
      if j.val ≤ 26 then
        8
      else
        0

def coreSelector212_70 (j : Fin 35) : Fin 46 :=
  if j.val ≤ 21 then
    if j.val ≤ 3 then
      12
    else
      if j.val ≤ 5 then
        11
      else
        10
  else
    if j.val ≤ 23 then
      9
    else
      if j.val ≤ 25 then
        8
      else
        0

def coreSelector212 (b : Fin 71) (j : Fin 35) : Fin 46 :=
  if b.val ≤ 34 then
    if b.val ≤ 16 then
      if b.val ≤ 7 then
        if b.val ≤ 3 then
          if b.val ≤ 1 then
            if b.val ≤ 0 then
              coreSelector212_0 j
            else
              coreSelector212_1 j
          else
            if b.val ≤ 2 then
              coreSelector212_2 j
            else
              coreSelector212_3 j
        else
          if b.val ≤ 5 then
            if b.val ≤ 4 then
              coreSelector212_4 j
            else
              coreSelector212_5 j
          else
            if b.val ≤ 6 then
              coreSelector212_6 j
            else
              coreSelector212_7 j
      else
        if b.val ≤ 11 then
          if b.val ≤ 9 then
            if b.val ≤ 8 then
              coreSelector212_8 j
            else
              coreSelector212_9 j
          else
            if b.val ≤ 10 then
              coreSelector212_10 j
            else
              coreSelector212_11 j
        else
          if b.val ≤ 13 then
            if b.val ≤ 12 then
              coreSelector212_12 j
            else
              coreSelector212_13 j
          else
            if b.val ≤ 14 then
              coreSelector212_14 j
            else
              if b.val ≤ 15 then
                coreSelector212_15 j
              else
                coreSelector212_16 j
    else
      if b.val ≤ 25 then
        if b.val ≤ 20 then
          if b.val ≤ 18 then
            if b.val ≤ 17 then
              coreSelector212_17 j
            else
              coreSelector212_18 j
          else
            if b.val ≤ 19 then
              coreSelector212_19 j
            else
              coreSelector212_20 j
        else
          if b.val ≤ 22 then
            if b.val ≤ 21 then
              coreSelector212_21 j
            else
              coreSelector212_22 j
          else
            if b.val ≤ 23 then
              coreSelector212_23 j
            else
              if b.val ≤ 24 then
                coreSelector212_24 j
              else
                coreSelector212_25 j
      else
        if b.val ≤ 29 then
          if b.val ≤ 27 then
            if b.val ≤ 26 then
              coreSelector212_26 j
            else
              coreSelector212_27 j
          else
            if b.val ≤ 28 then
              coreSelector212_28 j
            else
              coreSelector212_29 j
        else
          if b.val ≤ 31 then
            if b.val ≤ 30 then
              coreSelector212_30 j
            else
              coreSelector212_31 j
          else
            if b.val ≤ 32 then
              coreSelector212_32 j
            else
              if b.val ≤ 33 then
                coreSelector212_33 j
              else
                coreSelector212_34 j
  else
    if b.val ≤ 52 then
      if b.val ≤ 43 then
        if b.val ≤ 38 then
          if b.val ≤ 36 then
            if b.val ≤ 35 then
              coreSelector212_35 j
            else
              coreSelector212_36 j
          else
            if b.val ≤ 37 then
              coreSelector212_37 j
            else
              coreSelector212_38 j
        else
          if b.val ≤ 40 then
            if b.val ≤ 39 then
              coreSelector212_39 j
            else
              coreSelector212_40 j
          else
            if b.val ≤ 41 then
              coreSelector212_41 j
            else
              if b.val ≤ 42 then
                coreSelector212_42 j
              else
                coreSelector212_43 j
      else
        if b.val ≤ 47 then
          if b.val ≤ 45 then
            if b.val ≤ 44 then
              coreSelector212_44 j
            else
              coreSelector212_45 j
          else
            if b.val ≤ 46 then
              coreSelector212_46 j
            else
              coreSelector212_47 j
        else
          if b.val ≤ 49 then
            if b.val ≤ 48 then
              coreSelector212_48 j
            else
              coreSelector212_49 j
          else
            if b.val ≤ 50 then
              coreSelector212_50 j
            else
              if b.val ≤ 51 then
                coreSelector212_51 j
              else
                coreSelector212_52 j
    else
      if b.val ≤ 61 then
        if b.val ≤ 56 then
          if b.val ≤ 54 then
            if b.val ≤ 53 then
              coreSelector212_53 j
            else
              coreSelector212_54 j
          else
            if b.val ≤ 55 then
              coreSelector212_55 j
            else
              coreSelector212_56 j
        else
          if b.val ≤ 58 then
            if b.val ≤ 57 then
              coreSelector212_57 j
            else
              coreSelector212_58 j
          else
            if b.val ≤ 59 then
              coreSelector212_59 j
            else
              if b.val ≤ 60 then
                coreSelector212_60 j
              else
                coreSelector212_61 j
      else
        if b.val ≤ 65 then
          if b.val ≤ 63 then
            if b.val ≤ 62 then
              coreSelector212_62 j
            else
              coreSelector212_63 j
          else
            if b.val ≤ 64 then
              coreSelector212_64 j
            else
              coreSelector212_65 j
        else
          if b.val ≤ 67 then
            if b.val ≤ 66 then
              coreSelector212_66 j
            else
              coreSelector212_67 j
          else
            if b.val ≤ 68 then
              coreSelector212_68 j
            else
              if b.val ≤ 69 then
                coreSelector212_69 j
              else
                coreSelector212_70 j
def coreMetadataChunks212 (c : Fin 2) : List CoreOddData :=
  match c.val with
  | 0 => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨211, [211], [0, 0, 0, 0, 0]⟩, ⟨199, [199], [0, 0, 0, 0, 0]⟩, ⟨197, [197], [0, 0, 0, 0, 0]⟩, ⟨193, [193], [0, 0, 0, 0, 0]⟩, ⟨191, [191], [0, 0, 0, 0, 0]⟩, ⟨181, [181], [0, 0, 0, 0, 0]⟩, ⟨179, [179], [0, 0, 0, 0, 0]⟩, ⟨173, [173], [0, 0, 0, 0, 0]⟩, ⟨167, [167], [0, 0, 0, 0, 0]⟩, ⟨163, [163], [0, 0, 0, 0, 0]⟩, ⟨157, [157], [0, 0, 0, 0, 0]⟩, ⟨151, [151], [0, 0, 0, 0, 0]⟩, ⟨149, [149], [0, 0, 0, 0, 0]⟩, ⟨139, [139], [0, 0, 0, 0, 0]⟩, ⟨137, [137], [0, 0, 0, 0, 0]⟩, ⟨131, [131], [0, 0, 0, 0, 0]⟩, ⟨127, [127], [0, 0, 0, 0, 0]⟩, ⟨113, [113], [0, 0, 0, 0, 0]⟩, ⟨109, [109], [0, 0, 0, 0, 0]⟩, ⟨107, [107], [0, 0, 0, 0, 0]⟩, ⟨103, [103], [0, 0, 0, 0, 0]⟩, ⟨101, [101], [0, 0, 0, 0, 0]⟩, ⟨97, [97], [0, 0, 0, 0, 0]⟩, ⟨89, [89], [0, 0, 0, 0, 0]⟩, ⟨83, [83], [0, 0, 0, 0, 0]⟩, ⟨79, [79], [0, 0, 0, 0, 0]⟩, ⟨73, [73], [0, 0, 0, 0, 0]⟩, ⟨71, [71], [0, 0, 0, 0, 0]⟩, ⟨67, [67], [0, 0, 0, 0, 0]⟩, ⟨61, [61], [0, 0, 0, 0, 0]⟩, ⟨59, [59], [0, 0, 0, 0, 0]⟩, ⟨53, [53], [0, 0, 0, 0, 0]⟩, ⟨47, [47], [0, 0, 0, 0, 0]⟩, ⟨43, [43], [0, 0, 0, 0, 0]⟩, ⟨41, [41], [0, 0, 0, 0, 0]⟩, ⟨37, [37], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨169, [13, 13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨121, [11, 11], [0, 0, 0, 0, 1]⟩, ⟨209, [11, 19], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨49, [7, 7], [0, 0, 0, 1, 2]⟩, ⟨187, [11, 17], [0, 0, 0, 0, 1]⟩, ⟨143, [11, 13], [0, 0, 0, 0, 1]⟩, ⟨203, [7, 29], [0, 0, 0, 1, 2]⟩, ⟨161, [7, 23], [0, 0, 0, 1, 2]⟩, ⟨133, [7, 19], [0, 0, 0, 1, 2]⟩, ⟨119, [7, 17], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨125, [5, 5, 5], [0, 0, 1, 2, 4]⟩, ⟨91, [7, 13], [0, 0, 0, 1, 2]⟩, ⟨205, [5, 41], [0, 0, 1, 2, 4]⟩, ⟨77, [7, 11], [0, 0, 0, 1, 3]⟩, ⟨185, [5, 37], [0, 0, 1, 2, 4]⟩, ⟨155, [5, 31], [0, 0, 1, 2, 4]⟩, ⟨145, [5, 29], [0, 0, 1, 2, 4]⟩]
  | _ => [⟨115, [5, 23], [0, 0, 1, 2, 4]⟩, ⟨95, [5, 19], [0, 0, 1, 2, 4]⟩, ⟨85, [5, 17], [0, 0, 1, 2, 4]⟩, ⟨65, [5, 13], [0, 0, 1, 2, 4]⟩, ⟨55, [5, 11], [0, 0, 1, 2, 5]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨175, [5, 5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨81, [3, 3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨201, [3, 67], [0, 1, 2, 4, 8]⟩, ⟨183, [3, 61], [0, 1, 2, 4, 8]⟩, ⟨177, [3, 59], [0, 1, 2, 4, 8]⟩, ⟨159, [3, 53], [0, 1, 2, 4, 8]⟩, ⟨141, [3, 47], [0, 1, 2, 4, 8]⟩, ⟨129, [3, 43], [0, 1, 2, 4, 8]⟩, ⟨123, [3, 41], [0, 1, 2, 4, 8]⟩, ⟨111, [3, 37], [0, 1, 2, 4, 8]⟩, ⟨93, [3, 31], [0, 1, 2, 4, 8]⟩, ⟨87, [3, 29], [0, 1, 2, 4, 8]⟩, ⟨69, [3, 23], [0, 1, 2, 4, 8]⟩, ⟨207, [3, 3, 23], [0, 1, 2, 4, 8]⟩, ⟨57, [3, 19], [0, 1, 2, 4, 8]⟩, ⟨171, [3, 3, 19], [0, 1, 2, 4, 8]⟩, ⟨51, [3, 17], [0, 1, 2, 4, 8]⟩, ⟨153, [3, 3, 17], [0, 1, 2, 4, 8]⟩, ⟨39, [3, 13], [0, 1, 2, 4, 8]⟩, ⟨117, [3, 3, 13], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨99, [3, 3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨63, [3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨147, [3, 7, 7], [0, 1, 2, 5, 10]⟩, ⟨189, [3, 3, 3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩, ⟨45, [3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨75, [3, 5, 5], [0, 1, 3, 6, 12]⟩, ⟨135, [3, 3, 3, 5], [0, 1, 3, 6, 12]⟩, ⟨195, [3, 5, 13], [0, 1, 3, 6, 12]⟩, ⟨165, [3, 5, 11], [0, 1, 3, 6, 13]⟩, ⟨105, [3, 5, 7], [0, 1, 3, 7, 14]⟩]
end Erdos883Verified
