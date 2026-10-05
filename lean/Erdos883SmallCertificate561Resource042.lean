import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_42 :
    (List.ofFn coreChunks561_42).flatten =
      (coreData561.take (coreResources561 42).q).drop 86 := by
  decide +kernel

theorem coreCheck561_42 :
    ∀ c : Fin 1, (coreChunks561_42 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 42)) = true := by
  decide +kernel
#print axioms coreFlatten561_42
#print axioms coreCheck561_42
end Erdos883Verified
