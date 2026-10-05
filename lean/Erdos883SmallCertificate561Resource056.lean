import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_56 :
    (List.ofFn coreChunks561_56).flatten =
      (coreData561.take (coreResources561 56).q).drop 107 := by
  decide +kernel

theorem coreCheck561_56 :
    ∀ c : Fin 1, (coreChunks561_56 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 56)) = true := by
  decide +kernel
#print axioms coreFlatten561_56
#print axioms coreCheck561_56
end Erdos883Verified
