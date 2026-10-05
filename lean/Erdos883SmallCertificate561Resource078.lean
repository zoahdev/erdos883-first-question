import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_78 :
    (List.ofFn coreChunks561_78).flatten =
      (coreData561.take (coreResources561 78).q).drop 145 := by
  decide +kernel

theorem coreCheck561_78 :
    ∀ c : Fin 1, (coreChunks561_78 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 78)) = true := by
  decide +kernel
#print axioms coreFlatten561_78
#print axioms coreCheck561_78
end Erdos883Verified
