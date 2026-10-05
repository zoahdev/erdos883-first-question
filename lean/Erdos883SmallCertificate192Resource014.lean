import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_14 :
    (List.ofFn coreChunks192_14).flatten =
      (coreData192.take (coreResources192 14).q).drop 36 := by
  decide +kernel

theorem coreCheck192_14 :
    ∀ c : Fin 1, (coreChunks192_14 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 14)) = true := by
  decide +kernel
#print axioms coreFlatten192_14
#print axioms coreCheck192_14
end Erdos883Verified
