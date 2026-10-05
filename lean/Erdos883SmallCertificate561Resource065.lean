import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_65 :
    (List.ofFn coreChunks561_65).flatten =
      (coreData561.take (coreResources561 65).q).drop 122 := by
  decide +kernel

theorem coreCheck561_65 :
    ∀ c : Fin 1, (coreChunks561_65 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 65)) = true := by
  decide +kernel
#print axioms coreFlatten561_65
#print axioms coreCheck561_65
end Erdos883Verified
