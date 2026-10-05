import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_52 :
    (List.ofFn coreChunks561_52).flatten =
      (coreData561.take (coreResources561 52).q).drop 100 := by
  decide +kernel

theorem coreCheck561_52 :
    ∀ c : Fin 1, (coreChunks561_52 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 52)) = true := by
  decide +kernel
#print axioms coreFlatten561_52
#print axioms coreCheck561_52
end Erdos883Verified
