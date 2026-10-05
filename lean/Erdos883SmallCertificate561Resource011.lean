import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_11 :
    (List.ofFn coreChunks561_11).flatten =
      (coreData561.take (coreResources561 11).q).drop 104 := by
  decide +kernel

theorem coreCheck561_11 :
    ∀ c : Fin 1, (coreChunks561_11 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 11)) = true := by
  decide +kernel
#print axioms coreFlatten561_11
#print axioms coreCheck561_11
end Erdos883Verified
