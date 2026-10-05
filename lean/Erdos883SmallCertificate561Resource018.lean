import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_18 :
    (List.ofFn coreChunks561_18).flatten =
      (coreData561.take (coreResources561 18).q).drop 115 := by
  decide +kernel

theorem coreCheck561_18 :
    ∀ c : Fin 1, (coreChunks561_18 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 18)) = true := by
  decide +kernel
#print axioms coreFlatten561_18
#print axioms coreCheck561_18
end Erdos883Verified
