import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_67 :
    (List.ofFn coreChunks561_67).flatten =
      (coreData561.take (coreResources561 67).q).drop 124 := by
  decide +kernel

theorem coreCheck561_67 :
    ∀ c : Fin 1, (coreChunks561_67 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 67)) = true := by
  decide +kernel
#print axioms coreFlatten561_67
#print axioms coreCheck561_67
end Erdos883Verified
