import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_20 :
    (List.ofFn coreChunks561_20).flatten =
      (coreData561.take (coreResources561 20).q).drop 118 := by
  decide +kernel

theorem coreCheck561_20 :
    ∀ c : Fin 1, (coreChunks561_20 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 20)) = true := by
  decide +kernel
#print axioms coreFlatten561_20
#print axioms coreCheck561_20
end Erdos883Verified
