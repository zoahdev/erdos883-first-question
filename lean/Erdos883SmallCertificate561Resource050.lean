import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_50 :
    (List.ofFn coreChunks561_50).flatten =
      (coreData561.take (coreResources561 50).q).drop 96 := by
  decide +kernel

theorem coreCheck561_50 :
    ∀ c : Fin 1, (coreChunks561_50 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 50)) = true := by
  decide +kernel
#print axioms coreFlatten561_50
#print axioms coreCheck561_50
end Erdos883Verified
