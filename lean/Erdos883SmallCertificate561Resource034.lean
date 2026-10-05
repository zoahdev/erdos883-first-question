import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_34 :
    (List.ofFn coreChunks561_34).flatten =
      (coreData561.take (coreResources561 34).q).drop 138 := by
  decide +kernel

theorem coreCheck561_34 :
    ∀ c : Fin 1, (coreChunks561_34 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 34)) = true := by
  decide +kernel
#print axioms coreFlatten561_34
#print axioms coreCheck561_34
end Erdos883Verified
