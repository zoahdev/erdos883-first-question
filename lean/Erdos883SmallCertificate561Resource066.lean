import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_66 :
    (List.ofFn coreChunks561_66).flatten =
      (coreData561.take (coreResources561 66).q).drop 123 := by
  decide +kernel

theorem coreCheck561_66 :
    ∀ c : Fin 1, (coreChunks561_66 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 66)) = true := by
  decide +kernel
#print axioms coreFlatten561_66
#print axioms coreCheck561_66
end Erdos883Verified
