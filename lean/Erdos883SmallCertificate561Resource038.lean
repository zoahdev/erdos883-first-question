import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_38 :
    (List.ofFn coreChunks561_38).flatten =
      (coreData561.take (coreResources561 38).q).drop 73 := by
  decide +kernel

theorem coreCheck561_38 :
    ∀ c : Fin 1, (coreChunks561_38 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 38)) = true := by
  decide +kernel
#print axioms coreFlatten561_38
#print axioms coreCheck561_38
end Erdos883Verified
