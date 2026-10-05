import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_45 :
    (List.ofFn coreChunks561_45).flatten =
      (coreData561.take (coreResources561 45).q).drop 90 := by
  decide +kernel

theorem coreCheck561_45 :
    ∀ c : Fin 1, (coreChunks561_45 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 45)) = true := by
  decide +kernel
#print axioms coreFlatten561_45
#print axioms coreCheck561_45
end Erdos883Verified
