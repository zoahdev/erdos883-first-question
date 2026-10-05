import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_15 :
    (List.ofFn coreChunks561_15).flatten =
      (coreData561.take (coreResources561 15).q).drop 110 := by
  decide +kernel

theorem coreCheck561_15 :
    ∀ c : Fin 1, (coreChunks561_15 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 15)) = true := by
  decide +kernel
#print axioms coreFlatten561_15
#print axioms coreCheck561_15
end Erdos883Verified
