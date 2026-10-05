import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_72 :
    (List.ofFn coreChunks561_72).flatten =
      (coreData561.take (coreResources561 72).q).drop 134 := by
  decide +kernel

theorem coreCheck561_72 :
    ∀ c : Fin 1, (coreChunks561_72 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 72)) = true := by
  decide +kernel
#print axioms coreFlatten561_72
#print axioms coreCheck561_72
end Erdos883Verified
