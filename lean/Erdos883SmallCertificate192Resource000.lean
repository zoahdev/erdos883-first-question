import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_0 :
    (List.ofFn coreChunks192_0).flatten =
      (coreData192.take (coreResources192 0).q).drop 0 := by
  decide +kernel

theorem coreCheck192_0 :
    ∀ c : Fin 2, (coreChunks192_0 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 0)) = true := by
  decide +kernel
#print axioms coreFlatten192_0
#print axioms coreCheck192_0
end Erdos883Verified
