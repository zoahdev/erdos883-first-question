import Init
namespace Erdos883Verified
structure CoreOddData where
  value : Nat
  factors : List Nat
  signatures : List Nat
  deriving DecidableEq
structure CoreResourceData where
  q : Nat
  s : Nat
  bound : Nat
  evenPool : Bool
  deriving DecidableEq

def corePrimeSieveCount (X : Nat) : List Nat → Nat
  | [] => X
  | p :: ps => corePrimeSieveCount X ps - corePrimeSieveCount (X / p) ps

def coreDedup : List Nat → List Nat
  | [] => []
  | a :: xs => if a ∈ xs then coreDedup xs else a :: coreDedup xs

def coreResourceRowCheck (L : Nat) (data : List CoreOddData)
    (r : CoreResourceData) (u : CoreOddData) : Bool :=
  (data.take r.q).all fun v =>
    decide (u.value = v.value ∨ u.signatures.getD r.s 0 ≠ v.signatures.getD r.s 0 ∨
      r.bound ≤ corePrimeSieveCount (if r.evenPool then L / 2 else L)
        (coreDedup (u.factors ++ v.factors)))

def coreHalfOdds (U : Nat) := (U + 1) / 2
def coreRetainedOdds (U : Nat) := U / 3 - U / 6 + 1
def coreMaxHalfLength (U : Nat) := U / 6
def coreThreshold (U : Nat) := U / 2 + U / 3 - U / 6
def coreSignatureBudget (s : Nat) := if s = 0 then 0 else 2 ^ s + 1

def coreResourceRequirements (U plen b j : Nat) (r : CoreResourceData) : Prop :=
  let p := coreHalfOdds U - b - (j - coreSignatureBudget r.s - 1) / 2
  r.s ≤ plen ∧ p ≤ coreHalfOdds U ∧ p ≤ r.q ∧
    2 * (coreHalfOdds U - p - b) + coreSignatureBudget r.s < j ∧
    (if r.evenPool then b + j else U - coreThreshold U + coreMaxHalfLength U + j) ≤ r.bound
def coreNodup : List Nat → Bool
  | [] => true
  | a :: xs => (!xs.contains a) && coreNodup xs

def coreOrderCheck (U : Nat) (O : List Nat) : Bool :=
  coreNodup O && (decide (O.length = coreHalfOdds U) &&
    O.all (fun v => decide (1 ≤ v ∧ v ≤ U ∧ v % 2 = 1)))
def corePrimeCheck (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range (Nat.sqrt p + 1)).all
    (fun d => decide (d < 2 ∨ p % d ≠ 0))

def coreDivisorSignature : List Nat → Nat → Nat
  | [], _ => 0
  | p :: ps, v => (if v % p = 0 then 1 else 0) * 2 ^ ps.length + coreDivisorSignature ps v

def coreMetadataCheck (ps : List Nat) (data : List CoreOddData) : Bool :=
  data.all fun d => decide (d.factors.prod = d.value) &&
    (d.factors.all corePrimeCheck && (decide (d.value % 2 = 1) &&
      (List.range (ps.length + 1)).all (fun s =>
        decide (d.signatures.getD s 0 = coreDivisorSignature (ps.take s) d.value))))
def coreMergeFuel : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
      if x.ble y then x :: coreMergeFuel fuel xs (y :: ys)
      else y :: coreMergeFuel fuel (x :: xs) ys

def coreSortFuel : Nat → List Nat → List Nat
  | 0, xs => xs
  | fuel + 1, xs =>
      let k := xs.length / 2
      coreMergeFuel xs.length (coreSortFuel fuel (xs.take k)) (coreSortFuel fuel (xs.drop k))

def coreOrderPermutationCheck (U : Nat) (O : List Nat) : Bool :=
  decide (coreSortFuel (Nat.log2 O.length + 1) O = List.range' 1 (coreHalfOdds U) 2)
end Erdos883Verified
