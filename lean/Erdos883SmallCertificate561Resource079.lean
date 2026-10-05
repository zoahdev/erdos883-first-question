import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_79 :
    (List.ofFn coreChunks561_79).flatten =
      (coreData561.take (coreResources561 79).q).drop 146 := by
  decide +kernel

theorem coreCheck561_79 :
    ∀ c : Fin 1, (coreChunks561_79 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 79)) = true := by
  decide +kernel
#print axioms coreFlatten561_79
#print axioms coreCheck561_79
end Erdos883Verified
