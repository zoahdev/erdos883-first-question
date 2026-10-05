import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_91 :
    (List.ofFn coreChunks561_91).flatten =
      (coreData561.take (coreResources561 91).q).drop 185 := by
  decide +kernel

theorem coreCheck561_91 :
    ∀ c : Fin 1, (coreChunks561_91 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 91)) = true := by
  decide +kernel
#print axioms coreFlatten561_91
#print axioms coreCheck561_91
end Erdos883Verified
