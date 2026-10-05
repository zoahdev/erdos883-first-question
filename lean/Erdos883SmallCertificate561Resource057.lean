import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_57 :
    (List.ofFn coreChunks561_57).flatten =
      (coreData561.take (coreResources561 57).q).drop 109 := by
  decide +kernel

theorem coreCheck561_57 :
    ∀ c : Fin 1, (coreChunks561_57 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 57)) = true := by
  decide +kernel
#print axioms coreFlatten561_57
#print axioms coreCheck561_57
end Erdos883Verified
