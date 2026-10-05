import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_40 :
    (List.ofFn coreChunks561_40).flatten =
      (coreData561.take (coreResources561 40).q).drop 81 := by
  decide +kernel

theorem coreCheck561_40 :
    ∀ c : Fin 1, (coreChunks561_40 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 40)) = true := by
  decide +kernel
#print axioms coreFlatten561_40
#print axioms coreCheck561_40
end Erdos883Verified
