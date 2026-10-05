import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_19 :
    (List.ofFn coreChunks561_19).flatten =
      (coreData561.take (coreResources561 19).q).drop 117 := by
  decide +kernel

theorem coreCheck561_19 :
    ∀ c : Fin 1, (coreChunks561_19 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 19)) = true := by
  decide +kernel
#print axioms coreFlatten561_19
#print axioms coreCheck561_19
end Erdos883Verified
