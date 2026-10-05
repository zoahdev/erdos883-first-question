import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_12 :
    (List.ofFn coreChunks561_12).flatten =
      (coreData561.take (coreResources561 12).q).drop 107 := by
  decide +kernel

theorem coreCheck561_12 :
    ∀ c : Fin 1, (coreChunks561_12 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 12)) = true := by
  decide +kernel
#print axioms coreFlatten561_12
#print axioms coreCheck561_12
end Erdos883Verified
