import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_18 :
    (List.ofFn coreChunks192_18).flatten =
      (coreData192.take (coreResources192 18).q).drop 42 := by
  decide +kernel

theorem coreCheck192_18 :
    ∀ c : Fin 1, (coreChunks192_18 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 18)) = true := by
  decide +kernel
#print axioms coreFlatten192_18
#print axioms coreCheck192_18
end Erdos883Verified
