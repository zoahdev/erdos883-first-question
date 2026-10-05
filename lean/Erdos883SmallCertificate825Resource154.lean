import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_154 :
    (List.ofFn coreChunks825_154).flatten =
      (coreData825.take (coreResources825 154).q).drop 268 := by
  decide +kernel

theorem coreCheck825_154 :
    ∀ c : Fin 1, (coreChunks825_154 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 154)) = true := by
  decide +kernel
#print axioms coreFlatten825_154
#print axioms coreCheck825_154
end Erdos883Verified
