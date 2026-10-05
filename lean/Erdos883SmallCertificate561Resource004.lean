import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_4 :
    (List.ofFn coreChunks561_4).flatten =
      (coreData561.take (coreResources561 4).q).drop 65 := by
  decide +kernel

theorem coreCheck561_4 :
    ∀ c : Fin 1, (coreChunks561_4 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 4)) = true := by
  decide +kernel
#print axioms coreFlatten561_4
#print axioms coreCheck561_4
end Erdos883Verified
