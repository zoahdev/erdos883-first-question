import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_100 :
    (List.ofFn coreChunks561_100).flatten =
      (coreData561.take (coreResources561 100).q).drop 255 := by
  decide +kernel

theorem coreCheck561_100 :
    ∀ c : Fin 2, (coreChunks561_100 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 100)) = true := by
  decide +kernel
#print axioms coreFlatten561_100
#print axioms coreCheck561_100
end Erdos883Verified
