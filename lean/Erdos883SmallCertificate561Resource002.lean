import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_2 :
    (List.ofFn coreChunks561_2).flatten =
      (coreData561.take (coreResources561 2).q).drop 50 := by
  decide +kernel

theorem coreCheck561_2 :
    ∀ c : Fin 1, (coreChunks561_2 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 2)) = true := by
  decide +kernel
#print axioms coreFlatten561_2
#print axioms coreCheck561_2
end Erdos883Verified
