import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_60 :
    (List.ofFn coreChunks561_60).flatten =
      (coreData561.take (coreResources561 60).q).drop 113 := by
  decide +kernel

theorem coreCheck561_60 :
    ∀ c : Fin 1, (coreChunks561_60 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 60)) = true := by
  decide +kernel
#print axioms coreFlatten561_60
#print axioms coreCheck561_60
end Erdos883Verified
