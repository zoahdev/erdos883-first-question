import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_53 :
    (List.ofFn coreChunks561_53).flatten =
      (coreData561.take (coreResources561 53).q).drop 102 := by
  decide +kernel

theorem coreCheck561_53 :
    ∀ c : Fin 1, (coreChunks561_53 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 53)) = true := by
  decide +kernel
#print axioms coreFlatten561_53
#print axioms coreCheck561_53
end Erdos883Verified
