import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_23 :
    (List.ofFn coreChunks192_23).flatten =
      (coreData192.take (coreResources192 23).q).drop 48 := by
  decide +kernel

theorem coreCheck192_23 :
    ∀ c : Fin 1, (coreChunks192_23 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 23)) = true := by
  decide +kernel
#print axioms coreFlatten192_23
#print axioms coreCheck192_23
end Erdos883Verified
