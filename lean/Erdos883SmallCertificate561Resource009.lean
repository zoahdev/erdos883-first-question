import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_9 :
    (List.ofFn coreChunks561_9).flatten =
      (coreData561.take (coreResources561 9).q).drop 102 := by
  decide +kernel

theorem coreCheck561_9 :
    ∀ c : Fin 1, (coreChunks561_9 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 9)) = true := by
  decide +kernel
#print axioms coreFlatten561_9
#print axioms coreCheck561_9
end Erdos883Verified
