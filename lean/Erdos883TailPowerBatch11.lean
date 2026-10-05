import Erdos883TailPowerCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Erdos883Verified
theorem finiteTailPowerBatch11 : ∀ i : Fin 24, finiteTailPowerPredicate (264 + i.val) := by
  unfold finiteTailPowerPredicate
  decide +kernel
#print axioms finiteTailPowerBatch11
end Erdos883Verified
