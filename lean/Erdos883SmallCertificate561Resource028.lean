import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_28 :
    (List.ofFn coreChunks561_28).flatten =
      (coreData561.take (coreResources561 28).q).drop 126 := by
  decide +kernel

theorem coreCheck561_28 :
    ∀ c : Fin 1, (coreChunks561_28 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 28)) = true := by
  decide +kernel
#print axioms coreFlatten561_28
#print axioms coreCheck561_28
end Erdos883Verified
