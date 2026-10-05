import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_41 :
    (List.ofFn coreChunks561_41).flatten =
      (coreData561.take (coreResources561 41).q).drop 85 := by
  decide +kernel

theorem coreCheck561_41 :
    ∀ c : Fin 1, (coreChunks561_41 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 41)) = true := by
  decide +kernel
#print axioms coreFlatten561_41
#print axioms coreCheck561_41
end Erdos883Verified
