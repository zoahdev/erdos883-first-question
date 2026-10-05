import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_54 :
    (List.ofFn coreChunks561_54).flatten =
      (coreData561.take (coreResources561 54).q).drop 103 := by
  decide +kernel

theorem coreCheck561_54 :
    ∀ c : Fin 1, (coreChunks561_54 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 54)) = true := by
  decide +kernel
#print axioms coreFlatten561_54
#print axioms coreCheck561_54
end Erdos883Verified
