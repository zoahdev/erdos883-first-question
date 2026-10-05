import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_81 :
    (List.ofFn coreChunks561_81).flatten =
      (coreData561.take (coreResources561 81).q).drop 150 := by
  decide +kernel

theorem coreCheck561_81 :
    ∀ c : Fin 1, (coreChunks561_81 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 81)) = true := by
  decide +kernel
#print axioms coreFlatten561_81
#print axioms coreCheck561_81
end Erdos883Verified
