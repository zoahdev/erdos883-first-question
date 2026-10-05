import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_95 :
    (List.ofFn coreChunks561_95).flatten =
      (coreData561.take (coreResources561 95).q).drop 228 := by
  decide +kernel

theorem coreCheck561_95 :
    ∀ c : Fin 1, (coreChunks561_95 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 95)) = true := by
  decide +kernel
#print axioms coreFlatten561_95
#print axioms coreCheck561_95
end Erdos883Verified
