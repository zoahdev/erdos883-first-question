import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_48 :
    (List.ofFn coreChunks561_48).flatten =
      (coreData561.take (coreResources561 48).q).drop 93 := by
  decide +kernel

theorem coreCheck561_48 :
    ∀ c : Fin 1, (coreChunks561_48 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 48)) = true := by
  decide +kernel
#print axioms coreFlatten561_48
#print axioms coreCheck561_48
end Erdos883Verified
