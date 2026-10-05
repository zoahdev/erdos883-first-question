import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_17 :
    (List.ofFn coreChunks192_17).flatten =
      (coreData192.take (coreResources192 17).q).drop 40 := by
  decide +kernel

theorem coreCheck192_17 :
    ∀ c : Fin 1, (coreChunks192_17 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 17)) = true := by
  decide +kernel
#print axioms coreFlatten192_17
#print axioms coreCheck192_17
end Erdos883Verified
