import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_13 :
    (List.ofFn coreChunks561_13).flatten =
      (coreData561.take (coreResources561 13).q).drop 108 := by
  decide +kernel

theorem coreCheck561_13 :
    ∀ c : Fin 1, (coreChunks561_13 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 13)) = true := by
  decide +kernel
#print axioms coreFlatten561_13
#print axioms coreCheck561_13
end Erdos883Verified
