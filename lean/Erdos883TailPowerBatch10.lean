import Erdos883TailPowerCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Erdos883Verified
theorem finiteTailPowerBatch10 : ∀ i : Fin 24, finiteTailPowerPredicate (240 + i.val) := by
  unfold finiteTailPowerPredicate
  decide +kernel
#print axioms finiteTailPowerBatch10
end Erdos883Verified
