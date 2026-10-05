import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_63 :
    (List.ofFn coreChunks561_63).flatten =
      (coreData561.take (coreResources561 63).q).drop 119 := by
  decide +kernel

theorem coreCheck561_63 :
    ∀ c : Fin 1, (coreChunks561_63 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 63)) = true := by
  decide +kernel
#print axioms coreFlatten561_63
#print axioms coreCheck561_63
end Erdos883Verified
