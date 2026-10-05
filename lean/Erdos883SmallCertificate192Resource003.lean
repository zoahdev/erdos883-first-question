import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_3 :
    (List.ofFn coreChunks192_3).flatten =
      (coreData192.take (coreResources192 3).q).drop 27 := by
  decide +kernel

theorem coreCheck192_3 :
    ∀ c : Fin 1, (coreChunks192_3 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 3)) = true := by
  decide +kernel
#print axioms coreFlatten192_3
#print axioms coreCheck192_3
end Erdos883Verified
