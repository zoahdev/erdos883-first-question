import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_34 :
    (List.ofFn coreChunks192_34).flatten =
      (coreData192.take (coreResources192 34).q).drop 94 := by
  decide +kernel

theorem coreCheck192_34 :
    ∀ c : Fin 1, (coreChunks192_34 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 34)) = true := by
  decide +kernel
#print axioms coreFlatten192_34
#print axioms coreCheck192_34
end Erdos883Verified
