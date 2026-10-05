import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_97 :
    (List.ofFn coreChunks561_97).flatten =
      (coreData561.take (coreResources561 97).q).drop 234 := by
  decide +kernel

theorem coreCheck561_97 :
    ∀ c : Fin 1, (coreChunks561_97 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 97)) = true := by
  decide +kernel
#print axioms coreFlatten561_97
#print axioms coreCheck561_97
end Erdos883Verified
