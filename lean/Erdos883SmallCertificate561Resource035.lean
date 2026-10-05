import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_35 :
    (List.ofFn coreChunks561_35).flatten =
      (coreData561.take (coreResources561 35).q).drop 140 := by
  decide +kernel

theorem coreCheck561_35 :
    ∀ c : Fin 1, (coreChunks561_35 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 35)) = true := by
  decide +kernel
#print axioms coreFlatten561_35
#print axioms coreCheck561_35
end Erdos883Verified
