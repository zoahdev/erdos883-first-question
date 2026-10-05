import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_68 :
    (List.ofFn coreChunks561_68).flatten =
      (coreData561.take (coreResources561 68).q).drop 125 := by
  decide +kernel

theorem coreCheck561_68 :
    ∀ c : Fin 1, (coreChunks561_68 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 68)) = true := by
  decide +kernel
#print axioms coreFlatten561_68
#print axioms coreCheck561_68
end Erdos883Verified
