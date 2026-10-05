import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_16 :
    (List.ofFn coreChunks192_16).flatten =
      (coreData192.take (coreResources192 16).q).drop 38 := by
  decide +kernel

theorem coreCheck192_16 :
    ∀ c : Fin 1, (coreChunks192_16 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 16)) = true := by
  decide +kernel
#print axioms coreFlatten192_16
#print axioms coreCheck192_16
end Erdos883Verified
