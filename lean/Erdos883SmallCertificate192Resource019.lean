import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_19 :
    (List.ofFn coreChunks192_19).flatten =
      (coreData192.take (coreResources192 19).q).drop 44 := by
  decide +kernel

theorem coreCheck192_19 :
    ∀ c : Fin 1, (coreChunks192_19 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 19)) = true := by
  decide +kernel
#print axioms coreFlatten192_19
#print axioms coreCheck192_19
end Erdos883Verified
