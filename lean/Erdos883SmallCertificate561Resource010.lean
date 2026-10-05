import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_10 :
    (List.ofFn coreChunks561_10).flatten =
      (coreData561.take (coreResources561 10).q).drop 103 := by
  decide +kernel

theorem coreCheck561_10 :
    ∀ c : Fin 1, (coreChunks561_10 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 10)) = true := by
  decide +kernel
#print axioms coreFlatten561_10
#print axioms coreCheck561_10
end Erdos883Verified
