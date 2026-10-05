import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_32 :
    (List.ofFn coreChunks561_32).flatten =
      (coreData561.take (coreResources561 32).q).drop 136 := by
  decide +kernel

theorem coreCheck561_32 :
    ∀ c : Fin 1, (coreChunks561_32 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 32)) = true := by
  decide +kernel
#print axioms coreFlatten561_32
#print axioms coreCheck561_32
end Erdos883Verified
