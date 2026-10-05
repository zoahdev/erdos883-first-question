import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_14 :
    (List.ofFn coreChunks561_14).flatten =
      (coreData561.take (coreResources561 14).q).drop 109 := by
  decide +kernel

theorem coreCheck561_14 :
    ∀ c : Fin 1, (coreChunks561_14 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 14)) = true := by
  decide +kernel
#print axioms coreFlatten561_14
#print axioms coreCheck561_14
end Erdos883Verified
