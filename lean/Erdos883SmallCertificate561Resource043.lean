import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_43 :
    (List.ofFn coreChunks561_43).flatten =
      (coreData561.take (coreResources561 43).q).drop 88 := by
  decide +kernel

theorem coreCheck561_43 :
    ∀ c : Fin 1, (coreChunks561_43 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 43)) = true := by
  decide +kernel
#print axioms coreFlatten561_43
#print axioms coreCheck561_43
end Erdos883Verified
