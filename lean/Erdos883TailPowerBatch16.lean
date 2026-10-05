import Erdos883TailPowerCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Erdos883Verified
theorem finiteTailPowerBatch16 : ∀ i : Fin 24, finiteTailPowerPredicate (384 + i.val) := by
  unfold finiteTailPowerPredicate
  decide +kernel
#print axioms finiteTailPowerBatch16
end Erdos883Verified
