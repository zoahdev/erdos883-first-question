import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_51 :
    (List.ofFn coreChunks561_51).flatten =
      (coreData561.take (coreResources561 51).q).drop 98 := by
  decide +kernel

theorem coreCheck561_51 :
    ∀ c : Fin 1, (coreChunks561_51 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 51)) = true := by
  decide +kernel
#print axioms coreFlatten561_51
#print axioms coreCheck561_51
end Erdos883Verified
