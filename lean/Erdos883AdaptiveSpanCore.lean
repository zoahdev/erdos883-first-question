import Erdos883AdaptiveCertificateCore

namespace Erdos883Verified

/-- A lower bound valid throughout a closed interval of ranks. -/
structure AdaptiveDegreeSpan where
  lo : Nat
  hi : Nat
  minimum : Nat
  deriving DecidableEq

/-- A range-minimum tree whose leaves cover intervals rather than single ranks.
Every cached endpoint and every gap between children is checked. -/
inductive AdaptiveSpanTree where
  | leaf (lo hi minimum : Nat)
  | node (lo hi minimum : Nat) (left right : AdaptiveSpanTree)
  deriving DecidableEq

def AdaptiveSpanTree.low : AdaptiveSpanTree → Nat
  | .leaf lo _ _ => lo
  | .node lo _ _ _ _ => lo

def AdaptiveSpanTree.high : AdaptiveSpanTree → Nat
  | .leaf _ hi _ => hi
  | .node _ hi _ _ _ => hi

def AdaptiveSpanTree.minimum : AdaptiveSpanTree → Nat
  | .leaf _ _ m => m
  | .node _ _ m _ _ => m

def AdaptiveSpanTree.spans : AdaptiveSpanTree → List AdaptiveDegreeSpan
  | .leaf lo hi m => [⟨lo, hi, m⟩]
  | .node _ _ _ l r => l.spans ++ r.spans

def AdaptiveSpanTree.cacheCheck : AdaptiveSpanTree → Bool
  | .leaf lo hi _ => decide (lo ≤ hi)
  | .node lo hi m l r =>
      decide (lo = l.low ∧ hi = r.high ∧ l.high + 1 = r.low ∧
        m ≤ l.minimum ∧ m ≤ r.minimum) && l.cacheCheck && r.cacheCheck

/-- Check that the root covers all ranks below `n`. -/
def AdaptiveSpanTree.domainCheck (t : AdaptiveSpanTree) (n : Nat) : Bool :=
  decide (t.low = 0 ∧ n ≤ t.high + 1)

def AdaptiveSpanTree.LeafBounds (t : AdaptiveSpanTree) (F : Nat → Nat) : Prop :=
  ∀ sp ∈ t.spans, ∀ i, sp.lo ≤ i → i ≤ sp.hi → sp.minimum ≤ F i

/-- Certify a uniform bound on a queried interval using cached branch minima. -/
def AdaptiveSpanTree.rangeGe : AdaptiveSpanTree → Nat → Nat → Nat → Bool
  | t@(.leaf _ _ _), lo, hi, bound =>
      decide (hi < t.low ∨ t.high < lo ∨ bound ≤ t.minimum)
  | t@(.node _ _ _ l r), lo, hi, bound =>
      if hi < t.low ∨ t.high < lo ∨ bound ≤ t.minimum then true
      else l.rangeGe lo hi bound && r.rangeGe lo hi bound

def adaptiveSpanRankWitnessCheck (H bmax D j h : Nat) (w : AdaptiveRankWitness)
    (even whole : AdaptiveSpanTree) : Bool :=
  let a := (j-h-1)/2
  decide (h < j ∧ w.split ≤ bmax+1) &&
  ((if w.split = 0 then true else even.rangeGe a (a+w.split-1) (H+j-a)) &&
  (if w.split = bmax+1 then true else whole.rangeGe (a+w.split) (a+w.split) (D+j)))

end Erdos883Verified
