import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData35 : List CoreOddData :=
  [⟨1, [], [0, 0, 0, 0, 0]⟩,
   ⟨31, [31], [0, 0, 0, 0, 0]⟩,
   ⟨29, [29], [0, 0, 0, 0, 0]⟩,
   ⟨23, [23], [0, 0, 0, 0, 0]⟩,
   ⟨19, [19], [0, 0, 0, 0, 0]⟩,
   ⟨17, [17], [0, 0, 0, 0, 0]⟩,
   ⟨13, [13], [0, 0, 0, 0, 0]⟩,
   ⟨11, [11], [0, 0, 0, 0, 1]⟩,
   ⟨7, [7], [0, 0, 0, 1, 2]⟩,
   ⟨5, [5], [0, 0, 1, 2, 4]⟩,
   ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩,
   ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩,
   ⟨3, [3], [0, 1, 2, 4, 8]⟩,
   ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩,
   ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩]

def coreResources35 (i : Fin 9) : CoreResourceData :=
  if i.val ≤ 3 then
    if i.val ≤ 1 then
      if i.val ≤ 0 then
        ⟨6, 0, 16, true⟩
      else
        ⟨7, 0, 15, true⟩
    else
      if i.val ≤ 2 then
        ⟨8, 0, 14, true⟩
      else
        ⟨9, 0, 13, true⟩
  else
    if i.val ≤ 5 then
      if i.val ≤ 4 then
        ⟨11, 0, 11, true⟩
      else
        ⟨12, 0, 10, true⟩
    else
      if i.val ≤ 6 then
        ⟨15, 0, 7, true⟩
      else
        if i.val ≤ 7 then
          ⟨18, 0, 6, true⟩
        else
          ⟨15, 1, 10, true⟩

def coreChunks35_0 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks35_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩]

def coreChunks35_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩]

def coreChunks35_3 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩]

def coreChunks35_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks35_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨35, [5, 7], [0, 0, 1, 3, 6]⟩]

def coreChunks35_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks35_7 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩]

def coreChunks35_8 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreSelector35_0 (j : Fin 5) : Fin 9 :=
  7

def coreSelector35_1 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 3 then
    7
  else
    6

def coreSelector35_2 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 1 then
    7
  else
    6

def coreSelector35_3 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 3 then
    6
  else
    8

def coreSelector35_4 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 2 then
    6
  else
    if j.val ≤ 3 then
      8
    else
      5

def coreSelector35_5 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 1 then
    6
  else
    if j.val ≤ 3 then
      5
    else
      4

def coreSelector35_6 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 1 then
    5
  else
    4

def coreSelector35_7 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 3 then
    4
  else
    3

def coreSelector35_8 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 1 then
    4
  else
    if j.val ≤ 3 then
      3
    else
      2

def coreSelector35_9 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 1 then
    3
  else
    if j.val ≤ 3 then
      2
    else
      1

def coreSelector35_10 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 1 then
    2
  else
    if j.val ≤ 3 then
      1
    else
      0

def coreSelector35_11 (j : Fin 5) : Fin 9 :=
  if j.val ≤ 1 then
    1
  else
    0

def coreSelector35 (b : Fin 12) (j : Fin 5) : Fin 9 :=
  if b.val ≤ 5 then
    if b.val ≤ 2 then
      if b.val ≤ 0 then
        coreSelector35_0 j
      else
        if b.val ≤ 1 then
          coreSelector35_1 j
        else
          coreSelector35_2 j
    else
      if b.val ≤ 3 then
        coreSelector35_3 j
      else
        if b.val ≤ 4 then
          coreSelector35_4 j
        else
          coreSelector35_5 j
  else
    if b.val ≤ 8 then
      if b.val ≤ 6 then
        coreSelector35_6 j
      else
        if b.val ≤ 7 then
          coreSelector35_7 j
        else
          coreSelector35_8 j
    else
      if b.val ≤ 9 then
        coreSelector35_9 j
      else
        if b.val ≤ 10 then
          coreSelector35_10 j
        else
          coreSelector35_11 j
def coreMetadataChunks35 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨35, [5, 7], [0, 0, 1, 3, 6]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨33, [3, 11], [0, 1, 2, 4, 9]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩]
end Erdos883Verified
