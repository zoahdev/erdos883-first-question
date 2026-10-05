import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_3 :
    (List.ofFn coreChunks561_3).flatten =
      (coreData561.take (coreResources561 3).q).drop 64 := by
  decide +kernel

theorem coreCheck561_3 :
    ∀ c : Fin 1, (coreChunks561_3 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 3)) = true := by
  decide +kernel
#print axioms coreFlatten561_3
#print axioms coreCheck561_3
end Erdos883Verified
