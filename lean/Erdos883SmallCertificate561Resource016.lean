import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_16 :
    (List.ofFn coreChunks561_16).flatten =
      (coreData561.take (coreResources561 16).q).drop 112 := by
  decide +kernel

theorem coreCheck561_16 :
    ∀ c : Fin 1, (coreChunks561_16 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 16)) = true := by
  decide +kernel
#print axioms coreFlatten561_16
#print axioms coreCheck561_16
end Erdos883Verified
