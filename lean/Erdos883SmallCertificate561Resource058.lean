import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_58 :
    (List.ofFn coreChunks561_58).flatten =
      (coreData561.take (coreResources561 58).q).drop 110 := by
  decide +kernel

theorem coreCheck561_58 :
    ∀ c : Fin 1, (coreChunks561_58 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 58)) = true := by
  decide +kernel
#print axioms coreFlatten561_58
#print axioms coreCheck561_58
end Erdos883Verified
