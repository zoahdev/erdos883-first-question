import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_84 :
    (List.ofFn coreChunks561_84).flatten =
      (coreData561.take (coreResources561 84).q).drop 162 := by
  decide +kernel

theorem coreCheck561_84 :
    ∀ c : Fin 1, (coreChunks561_84 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 84)) = true := by
  decide +kernel
#print axioms coreFlatten561_84
#print axioms coreCheck561_84
end Erdos883Verified
