import Erdos883SmallCertificateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def coreData31 : List CoreOddData :=
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
   ⟨3, [3], [0, 1, 2, 4, 8]⟩,
   ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩,
   ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩,
   ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩]

def coreResources31 (i : Fin 8) : CoreResourceData :=
  if i.val ≤ 3 then
    if i.val ≤ 1 then
      if i.val ≤ 0 then
        ⟨4, 0, 27, false⟩
      else
        ⟨6, 0, 14, true⟩
    else
      if i.val ≤ 2 then
        ⟨7, 0, 13, true⟩
      else
        ⟨8, 0, 12, true⟩
  else
    if i.val ≤ 5 then
      if i.val ≤ 4 then
        ⟨9, 0, 11, true⟩
      else
        ⟨11, 0, 10, true⟩
    else
      if i.val ≤ 6 then
        ⟨14, 0, 8, true⟩
      else
        ⟨16, 0, 6, true⟩

def coreChunks31_0 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩]

def coreChunks31_1 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩]

def coreChunks31_2 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨13, [13], [0, 0, 0, 0, 0]⟩]

def coreChunks31_3 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨11, [11], [0, 0, 0, 0, 1]⟩]

def coreChunks31_4 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨7, [7], [0, 0, 0, 1, 2]⟩]

def coreChunks31_5 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩]

def coreChunks31_6 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩]

def coreChunks31_7 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩]

def coreSelector31_0 (j : Fin 5) : Fin 8 :=
  if j.val ≤ 3 then
    7
  else
    6

def coreSelector31_1 (j : Fin 5) : Fin 8 :=
  if j.val ≤ 1 then
    7
  else
    6

def coreSelector31_2 (j : Fin 5) : Fin 8 :=
  6

def coreSelector31_3 (j : Fin 5) : Fin 8 :=
  if j.val ≤ 3 then
    6
  else
    5

def coreSelector31_4 (j : Fin 5) : Fin 8 :=
  if j.val ≤ 1 then
    6
  else
    5

def coreSelector31_5 (j : Fin 5) : Fin 8 :=
  if j.val ≤ 3 then
    5
  else
    4

def coreSelector31_6 (j : Fin 5) : Fin 8 :=
  if j.val ≤ 1 then
    5
  else
    if j.val ≤ 3 then
      4
    else
      3

def coreSelector31_7 (j : Fin 5) : Fin 8 :=
  if j.val ≤ 1 then
    4
  else
    if j.val ≤ 3 then
      3
    else
      2

def coreSelector31_8 (j : Fin 5) : Fin 8 :=
  if j.val ≤ 1 then
    3
  else
    if j.val ≤ 3 then
      2
    else
      1

def coreSelector31_9 (j : Fin 5) : Fin 8 :=
  if j.val ≤ 1 then
    2
  else
    1

def coreSelector31_10 (j : Fin 5) : Fin 8 :=
  if j.val ≤ 3 then
    1
  else
    0

def coreSelector31 (b : Fin 11) (j : Fin 5) : Fin 8 :=
  if b.val ≤ 4 then
    if b.val ≤ 1 then
      if b.val ≤ 0 then
        coreSelector31_0 j
      else
        coreSelector31_1 j
    else
      if b.val ≤ 2 then
        coreSelector31_2 j
      else
        if b.val ≤ 3 then
          coreSelector31_3 j
        else
          coreSelector31_4 j
  else
    if b.val ≤ 7 then
      if b.val ≤ 5 then
        coreSelector31_5 j
      else
        if b.val ≤ 6 then
          coreSelector31_6 j
        else
          coreSelector31_7 j
    else
      if b.val ≤ 8 then
        coreSelector31_8 j
      else
        if b.val ≤ 9 then
          coreSelector31_9 j
        else
          coreSelector31_10 j
def coreMetadataChunks31 (c : Fin 1) : List CoreOddData :=
  match c.val with
  | _ => [⟨1, [], [0, 0, 0, 0, 0]⟩, ⟨31, [31], [0, 0, 0, 0, 0]⟩, ⟨29, [29], [0, 0, 0, 0, 0]⟩, ⟨23, [23], [0, 0, 0, 0, 0]⟩, ⟨19, [19], [0, 0, 0, 0, 0]⟩, ⟨17, [17], [0, 0, 0, 0, 0]⟩, ⟨13, [13], [0, 0, 0, 0, 0]⟩, ⟨11, [11], [0, 0, 0, 0, 1]⟩, ⟨7, [7], [0, 0, 0, 1, 2]⟩, ⟨5, [5], [0, 0, 1, 2, 4]⟩, ⟨25, [5, 5], [0, 0, 1, 2, 4]⟩, ⟨3, [3], [0, 1, 2, 4, 8]⟩, ⟨9, [3, 3], [0, 1, 2, 4, 8]⟩, ⟨27, [3, 3, 3], [0, 1, 2, 4, 8]⟩, ⟨21, [3, 7], [0, 1, 2, 5, 10]⟩, ⟨15, [3, 5], [0, 1, 3, 6, 12]⟩]
end Erdos883Verified
