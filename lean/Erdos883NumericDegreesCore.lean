import Init
namespace Erdos883Verified
/-- Exact natural arithmetic for an adaptive rational density lower bound. -/
def coreNumericDegree (scale W c d a b : Nat) : Nat :=
  scale * max (a ^ 2 * d) (a * b * c) / (b ^ 2 * d) - (2 ^ (W - 1) - 1)
end Erdos883Verified
