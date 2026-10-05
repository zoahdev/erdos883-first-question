import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_44 :
    (List.ofFn coreChunks561_44).flatten =
      (coreData561.take (coreResources561 44).q).drop 89 := by
  decide +kernel

theorem coreCheck561_44 :
    ∀ c : Fin 1, (coreChunks561_44 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 44)) = true := by
  decide +kernel
#print axioms coreFlatten561_44
#print axioms coreCheck561_44
end Erdos883Verified
