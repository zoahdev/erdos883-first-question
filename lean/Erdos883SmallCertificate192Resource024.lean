import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_24 :
    (List.ofFn coreChunks192_24).flatten =
      (coreData192.take (coreResources192 24).q).drop 49 := by
  decide +kernel

theorem coreCheck192_24 :
    ∀ c : Fin 1, (coreChunks192_24 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 24)) = true := by
  decide +kernel
#print axioms coreFlatten192_24
#print axioms coreCheck192_24
end Erdos883Verified
