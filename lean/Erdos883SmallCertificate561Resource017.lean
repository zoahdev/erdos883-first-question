import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_17 :
    (List.ofFn coreChunks561_17).flatten =
      (coreData561.take (coreResources561 17).q).drop 113 := by
  decide +kernel

theorem coreCheck561_17 :
    ∀ c : Fin 1, (coreChunks561_17 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 17)) = true := by
  decide +kernel
#print axioms coreFlatten561_17
#print axioms coreCheck561_17
end Erdos883Verified
