import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_61 :
    (List.ofFn coreChunks561_61).flatten =
      (coreData561.take (coreResources561 61).q).drop 115 := by
  decide +kernel

theorem coreCheck561_61 :
    ∀ c : Fin 1, (coreChunks561_61 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 61)) = true := by
  decide +kernel
#print axioms coreFlatten561_61
#print axioms coreCheck561_61
end Erdos883Verified
