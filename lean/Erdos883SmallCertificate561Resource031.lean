import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_31 :
    (List.ofFn coreChunks561_31).flatten =
      (coreData561.take (coreResources561 31).q).drop 134 := by
  decide +kernel

theorem coreCheck561_31 :
    ∀ c : Fin 1, (coreChunks561_31 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 31)) = true := by
  decide +kernel
#print axioms coreFlatten561_31
#print axioms coreCheck561_31
end Erdos883Verified
