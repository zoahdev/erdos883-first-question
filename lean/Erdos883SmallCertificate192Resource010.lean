import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_10 :
    (List.ofFn coreChunks192_10).flatten =
      (coreData192.take (coreResources192 10).q).drop 30 := by
  decide +kernel

theorem coreCheck192_10 :
    ∀ c : Fin 1, (coreChunks192_10 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 10)) = true := by
  decide +kernel
#print axioms coreFlatten192_10
#print axioms coreCheck192_10
end Erdos883Verified
