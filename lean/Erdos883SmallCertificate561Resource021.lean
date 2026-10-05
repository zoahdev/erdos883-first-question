import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_21 :
    (List.ofFn coreChunks561_21).flatten =
      (coreData561.take (coreResources561 21).q).drop 119 := by
  decide +kernel

theorem coreCheck561_21 :
    ∀ c : Fin 1, (coreChunks561_21 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 21)) = true := by
  decide +kernel
#print axioms coreFlatten561_21
#print axioms coreCheck561_21
end Erdos883Verified
