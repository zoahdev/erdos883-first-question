import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_1 :
    (List.ofFn coreChunks561_1).flatten =
      (coreData561.take (coreResources561 1).q).drop 49 := by
  decide +kernel

theorem coreCheck561_1 :
    ∀ c : Fin 1, (coreChunks561_1 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 1)) = true := by
  decide +kernel
#print axioms coreFlatten561_1
#print axioms coreCheck561_1
end Erdos883Verified
