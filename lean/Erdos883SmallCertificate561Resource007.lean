import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_7 :
    (List.ofFn coreChunks561_7).flatten =
      (coreData561.take (coreResources561 7).q).drop 76 := by
  decide +kernel

theorem coreCheck561_7 :
    ∀ c : Fin 2, (coreChunks561_7 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 7)) = true := by
  decide +kernel
#print axioms coreFlatten561_7
#print axioms coreCheck561_7
end Erdos883Verified
