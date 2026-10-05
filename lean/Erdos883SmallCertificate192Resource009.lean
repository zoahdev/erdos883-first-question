import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_9 :
    (List.ofFn coreChunks192_9).flatten =
      (coreData192.take (coreResources192 9).q).drop 22 := by
  decide +kernel

theorem coreCheck192_9 :
    ∀ c : Fin 1, (coreChunks192_9 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 9)) = true := by
  decide +kernel
#print axioms coreFlatten192_9
#print axioms coreCheck192_9
end Erdos883Verified
