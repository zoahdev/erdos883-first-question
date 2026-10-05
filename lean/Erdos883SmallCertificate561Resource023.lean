import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_23 :
    (List.ofFn coreChunks561_23).flatten =
      (coreData561.take (coreResources561 23).q).drop 121 := by
  decide +kernel

theorem coreCheck561_23 :
    ∀ c : Fin 1, (coreChunks561_23 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 23)) = true := by
  decide +kernel
#print axioms coreFlatten561_23
#print axioms coreCheck561_23
end Erdos883Verified
