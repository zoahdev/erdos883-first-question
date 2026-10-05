import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_93 :
    (List.ofFn coreChunks561_93).flatten =
      (coreData561.take (coreResources561 93).q).drop 201 := by
  decide +kernel

theorem coreCheck561_93 :
    ∀ c : Fin 1, (coreChunks561_93 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 93)) = true := by
  decide +kernel
#print axioms coreFlatten561_93
#print axioms coreCheck561_93
end Erdos883Verified
