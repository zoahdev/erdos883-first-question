import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_22 :
    (List.ofFn coreChunks192_22).flatten =
      (coreData192.take (coreResources192 22).q).drop 47 := by
  decide +kernel

theorem coreCheck192_22 :
    ∀ c : Fin 1, (coreChunks192_22 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 22)) = true := by
  decide +kernel
#print axioms coreFlatten192_22
#print axioms coreCheck192_22
end Erdos883Verified
