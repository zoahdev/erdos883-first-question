import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_74 :
    (List.ofFn coreChunks561_74).flatten =
      (coreData561.take (coreResources561 74).q).drop 138 := by
  decide +kernel

theorem coreCheck561_74 :
    ∀ c : Fin 1, (coreChunks561_74 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 74)) = true := by
  decide +kernel
#print axioms coreFlatten561_74
#print axioms coreCheck561_74
end Erdos883Verified
