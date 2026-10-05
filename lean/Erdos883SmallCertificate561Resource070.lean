import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_70 :
    (List.ofFn coreChunks561_70).flatten =
      (coreData561.take (coreResources561 70).q).drop 129 := by
  decide +kernel

theorem coreCheck561_70 :
    ∀ c : Fin 1, (coreChunks561_70 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 70)) = true := by
  decide +kernel
#print axioms coreFlatten561_70
#print axioms coreCheck561_70
end Erdos883Verified
