import Init
namespace Erdos883Verified

/-- A certificate tree for finitely many indexed nonnegative values. Caches are
verified separately; the tree's shape is not trusted. -/
inductive AdaptiveMinTree where
  | leaf (index value : Nat)
  | node (lo hi minimum : Nat) (left right : AdaptiveMinTree)
  deriving DecidableEq

def AdaptiveMinTree.low : AdaptiveMinTree → Nat
  | .leaf i _ => i
  | .node lo _ _ _ _ => lo

def AdaptiveMinTree.high : AdaptiveMinTree → Nat
  | .leaf i _ => i
  | .node _ hi _ _ _ => hi

def AdaptiveMinTree.minimum : AdaptiveMinTree → Nat
  | .leaf _ v => v
  | .node _ _ m _ _ => m

def AdaptiveMinTree.entries : AdaptiveMinTree → List (Nat × Nat)
  | .leaf i v => [(i,v)]
  | .node _ _ _ l r => l.entries ++ r.entries

def AdaptiveMinTree.cacheCheck : AdaptiveMinTree → Bool
  | .leaf _ _ => true
  | .node lo hi m l r =>
    decide (lo ≤ l.low ∧ lo ≤ r.low ∧ l.high ≤ hi ∧ r.high ≤ hi ∧
      m ≤ l.minimum ∧ m ≤ r.minimum) && l.cacheCheck && r.cacheCheck

/-- Verify a range lower bound. Caches allow whole branches to be discarded. -/
def AdaptiveMinTree.rangeGe : AdaptiveMinTree → Nat → Nat → Nat → Bool
  | t@(.leaf i v), lo, hi, bound =>
      decide (hi < t.low ∨ t.high < lo ∨ bound ≤ t.minimum)
  | t@(.node _ _ _ l r), lo, hi, bound =>
      if hi < t.low ∨ t.high < lo ∨ bound ≤ t.minimum then true
      else l.rangeGe lo hi bound && r.rangeGe lo hi bound

structure AdaptiveRankWitness where
  s : Nat
  split : Nat
  deriving DecidableEq

/-- For ranks below `split`, the shifted even degree is checked. Above that
split, a single monotone whole-pool rank suffices. -/
def adaptiveRankWitnessCheck (H bmax D j h : Nat) (w : AdaptiveRankWitness)
    (even whole : AdaptiveMinTree) : Bool :=
  let a := (j-h-1)/2
  decide (h < j ∧ w.split ≤ bmax+1) &&
  ((if w.split = 0 then true else even.rangeGe a (a+w.split-1) (H+j-a)) &&
  (if w.split = bmax+1 then true else whole.rangeGe (a+w.split) (a+w.split) (D+j)))
end Erdos883Verified
