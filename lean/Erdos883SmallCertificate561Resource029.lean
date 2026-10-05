import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_29 :
    (List.ofFn coreChunks561_29).flatten =
      (coreData561.take (coreResources561 29).q).drop 129 := by
  decide +kernel

theorem coreCheck561_29 :
    ∀ c : Fin 1, (coreChunks561_29 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 29)) = true := by
  decide +kernel
#print axioms coreFlatten561_29
#print axioms coreCheck561_29
end Erdos883Verified
