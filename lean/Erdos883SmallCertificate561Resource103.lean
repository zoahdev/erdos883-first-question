import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_103 :
    (List.ofFn coreChunks561_103).flatten =
      (coreData561.take (coreResources561 103).q).drop 180 := by
  decide +kernel

theorem coreCheck561_103 :
    ∀ c : Fin 1, (coreChunks561_103 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 103)) = true := by
  decide +kernel
#print axioms coreFlatten561_103
#print axioms coreCheck561_103
end Erdos883Verified
