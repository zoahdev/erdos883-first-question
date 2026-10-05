import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_33 :
    (List.ofFn coreChunks561_33).flatten =
      (coreData561.take (coreResources561 33).q).drop 137 := by
  decide +kernel

theorem coreCheck561_33 :
    ∀ c : Fin 1, (coreChunks561_33 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 33)) = true := by
  decide +kernel
#print axioms coreFlatten561_33
#print axioms coreCheck561_33
end Erdos883Verified
