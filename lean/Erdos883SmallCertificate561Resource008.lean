import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_8 :
    (List.ofFn coreChunks561_8).flatten =
      (coreData561.take (coreResources561 8).q).drop 100 := by
  decide +kernel

theorem coreCheck561_8 :
    ∀ c : Fin 1, (coreChunks561_8 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 8)) = true := by
  decide +kernel
#print axioms coreFlatten561_8
#print axioms coreCheck561_8
end Erdos883Verified
