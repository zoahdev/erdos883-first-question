import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_90 :
    (List.ofFn coreChunks561_90).flatten =
      (coreData561.take (coreResources561 90).q).drop 178 := by
  decide +kernel

theorem coreCheck561_90 :
    ∀ c : Fin 1, (coreChunks561_90 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 90)) = true := by
  decide +kernel
#print axioms coreFlatten561_90
#print axioms coreCheck561_90
end Erdos883Verified
