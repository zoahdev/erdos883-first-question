import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_28 :
    (List.ofFn coreChunks192_28).flatten =
      (coreData192.take (coreResources192 28).q).drop 58 := by
  decide +kernel

theorem coreCheck192_28 :
    ∀ c : Fin 1, (coreChunks192_28 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 28)) = true := by
  decide +kernel
#print axioms coreFlatten192_28
#print axioms coreCheck192_28
end Erdos883Verified
