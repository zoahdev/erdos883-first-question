import Erdos883TailPowerCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Erdos883Verified
theorem finiteTailPowerBatch04 : ∀ i : Fin 24, finiteTailPowerPredicate (96 + i.val) := by
  unfold finiteTailPowerPredicate
  decide +kernel
#print axioms finiteTailPowerBatch04
end Erdos883Verified
