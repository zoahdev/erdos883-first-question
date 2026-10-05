import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_87 :
    (List.ofFn coreChunks561_87).flatten =
      (coreData561.take (coreResources561 87).q).drop 171 := by
  decide +kernel

theorem coreCheck561_87 :
    ∀ c : Fin 1, (coreChunks561_87 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 87)) = true := by
  decide +kernel
#print axioms coreFlatten561_87
#print axioms coreCheck561_87
end Erdos883Verified
