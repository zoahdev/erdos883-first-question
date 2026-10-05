import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_4 :
    (List.ofFn coreChunks192_4).flatten =
      (coreData192.take (coreResources192 4).q).drop 43 := by
  decide +kernel

theorem coreCheck192_4 :
    ∀ c : Fin 1, (coreChunks192_4 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 4)) = true := by
  decide +kernel
#print axioms coreFlatten192_4
#print axioms coreCheck192_4
end Erdos883Verified
