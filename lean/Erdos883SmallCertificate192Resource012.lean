import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_12 :
    (List.ofFn coreChunks192_12).flatten =
      (coreData192.take (coreResources192 12).q).drop 34 := by
  decide +kernel

theorem coreCheck192_12 :
    ∀ c : Fin 1, (coreChunks192_12 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 12)) = true := by
  decide +kernel
#print axioms coreFlatten192_12
#print axioms coreCheck192_12
end Erdos883Verified
