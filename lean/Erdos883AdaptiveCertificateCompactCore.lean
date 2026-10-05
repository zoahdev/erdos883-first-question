import Erdos883AdaptiveCertificateDataCore
namespace Erdos883Verified
/-- Compact decimal data are decoded by ordinary structural recursion. -/
def adaptiveDecodeAux : List Char → Nat → List Nat
  | [], n => [n]
  | c :: cs, n => if c = ',' then n :: adaptiveDecodeAux cs 0
      else adaptiveDecodeAux cs (10*n+c.toNat-48)

def adaptiveDecode (s : String) : List Nat := adaptiveDecodeAux s.toList 0

def adaptiveBuildTree : Nat → Nat → List Nat → AdaptiveMinTree
  | 0, start, xs => .leaf start (xs.headD 0)
  | fuel+1, start, xs =>
    if xs.length ≤ 1 then .leaf start (xs.headD 0)
    else
      let k := xs.length/2
      let l := adaptiveBuildTree fuel start (xs.take k)
      let r := adaptiveBuildTree fuel (start+k) (xs.drop k)
      .node l.low r.high (min l.minimum r.minimum) l r

def adaptiveCompactTree (s : String) : AdaptiveMinTree :=
  let xs := adaptiveDecode s
  adaptiveBuildTree (Nat.log2 xs.length + 1) 0 xs
def adaptiveDecodeRows : Nat → List Nat → List AdaptiveProfileRow
  | 0, _ => []
  | fuel+1, n :: num :: k :: rest =>
      ⟨n, rest.take k, num⟩ :: adaptiveDecodeRows fuel (rest.drop k)
  | _+1, _ => []

def adaptiveCompactRows (count : Nat) (s : String) : List AdaptiveProfileRow :=
  adaptiveDecodeRows count (adaptiveDecode s)
/-- Base-2^20 packed natural data; kernel arithmetic decodes each digit. -/
def adaptiveUnpack : Nat → Nat → List Nat
  | 0, _ => []
  | count+1, packed => packed % 1048576 :: adaptiveUnpack count (packed / 1048576)

def adaptivePackedTreeAt (start count packed : Nat) : AdaptiveMinTree :=
  adaptiveBuildTree (Nat.log2 count + 1) start (adaptiveUnpack count packed)

def adaptivePackedTree (count packed : Nat) : AdaptiveMinTree :=
  adaptivePackedTreeAt 0 count packed

def adaptivePackedRows (count entries packed : Nat) : List AdaptiveProfileRow :=
  adaptiveDecodeRows count (adaptiveUnpack entries packed)
theorem coreProfileMetadataCheck_flatten (chunks : List (List AdaptiveProfileRow)) :
    coreProfileMetadataCheck chunks.flatten = chunks.all coreProfileMetadataCheck := by
  simp only [coreProfileMetadataCheck, List.all_flatten]
  rfl
end Erdos883Verified
