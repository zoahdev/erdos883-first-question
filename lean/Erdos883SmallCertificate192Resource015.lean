import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_15 :
    (List.ofFn coreChunks192_15).flatten =
      (coreData192.take (coreResources192 15).q).drop 37 := by
  decide +kernel

theorem coreCheck192_15 :
    ∀ c : Fin 1, (coreChunks192_15 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 15)) = true := by
  decide +kernel
#print axioms coreFlatten192_15
#print axioms coreCheck192_15
end Erdos883Verified
