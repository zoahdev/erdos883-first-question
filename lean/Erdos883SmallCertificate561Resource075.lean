import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_75 :
    (List.ofFn coreChunks561_75).flatten =
      (coreData561.take (coreResources561 75).q).drop 140 := by
  decide +kernel

theorem coreCheck561_75 :
    ∀ c : Fin 1, (coreChunks561_75 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 75)) = true := by
  decide +kernel
#print axioms coreFlatten561_75
#print axioms coreCheck561_75
end Erdos883Verified
