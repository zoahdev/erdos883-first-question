import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten313_53 :
    (List.ofFn coreChunks313_53).flatten =
      (coreData313.take (coreResources313 53).q).drop 150 := by
  decide +kernel

theorem coreCheck313_53 :
    ∀ c : Fin 1, (coreChunks313_53 c).all
      (coreResourceRowCheck 285 coreData313 (coreResources313 53)) = true := by
  decide +kernel
#print axioms coreFlatten313_53
#print axioms coreCheck313_53
end Erdos883Verified
