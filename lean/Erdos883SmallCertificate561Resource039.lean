import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_39 :
    (List.ofFn coreChunks561_39).flatten =
      (coreData561.take (coreResources561 39).q).drop 80 := by
  decide +kernel

theorem coreCheck561_39 :
    ∀ c : Fin 1, (coreChunks561_39 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 39)) = true := by
  decide +kernel
#print axioms coreFlatten561_39
#print axioms coreCheck561_39
end Erdos883Verified
