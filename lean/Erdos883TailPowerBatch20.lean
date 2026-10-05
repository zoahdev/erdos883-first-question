import Erdos883TailPowerCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Erdos883Verified
theorem finiteTailPowerBatch20 : ∀ i : Fin 22, finiteTailPowerPredicate (480 + i.val) := by
  unfold finiteTailPowerPredicate
  decide +kernel
#print axioms finiteTailPowerBatch20
end Erdos883Verified
