import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_26 :
    (List.ofFn coreChunks561_26).flatten =
      (coreData561.take (coreResources561 26).q).drop 124 := by
  decide +kernel

theorem coreCheck561_26 :
    ∀ c : Fin 1, (coreChunks561_26 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 26)) = true := by
  decide +kernel
#print axioms coreFlatten561_26
#print axioms coreCheck561_26
end Erdos883Verified
