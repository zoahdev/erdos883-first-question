import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_49 :
    (List.ofFn coreChunks561_49).flatten =
      (coreData561.take (coreResources561 49).q).drop 94 := by
  decide +kernel

theorem coreCheck561_49 :
    ∀ c : Fin 1, (coreChunks561_49 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 49)) = true := by
  decide +kernel
#print axioms coreFlatten561_49
#print axioms coreCheck561_49
end Erdos883Verified
