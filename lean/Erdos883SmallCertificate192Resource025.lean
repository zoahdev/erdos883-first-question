import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_25 :
    (List.ofFn coreChunks192_25).flatten =
      (coreData192.take (coreResources192 25).q).drop 52 := by
  decide +kernel

theorem coreCheck192_25 :
    ∀ c : Fin 1, (coreChunks192_25 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 25)) = true := by
  decide +kernel
#print axioms coreFlatten192_25
#print axioms coreCheck192_25
end Erdos883Verified
