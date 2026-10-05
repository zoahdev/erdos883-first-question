import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_26 :
    (List.ofFn coreChunks192_26).flatten =
      (coreData192.take (coreResources192 26).q).drop 54 := by
  decide +kernel

theorem coreCheck192_26 :
    ∀ c : Fin 1, (coreChunks192_26 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 26)) = true := by
  decide +kernel
#print axioms coreFlatten192_26
#print axioms coreCheck192_26
end Erdos883Verified
