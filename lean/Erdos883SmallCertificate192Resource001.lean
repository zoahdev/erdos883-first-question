import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_1 :
    (List.ofFn coreChunks192_1).flatten =
      (coreData192.take (coreResources192 1).q).drop 21 := by
  decide +kernel

theorem coreCheck192_1 :
    ∀ c : Fin 1, (coreChunks192_1 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 1)) = true := by
  decide +kernel
#print axioms coreFlatten192_1
#print axioms coreCheck192_1
end Erdos883Verified
