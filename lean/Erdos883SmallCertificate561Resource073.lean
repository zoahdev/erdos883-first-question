import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_73 :
    (List.ofFn coreChunks561_73).flatten =
      (coreData561.take (coreResources561 73).q).drop 137 := by
  decide +kernel

theorem coreCheck561_73 :
    ∀ c : Fin 1, (coreChunks561_73 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 73)) = true := by
  decide +kernel
#print axioms coreFlatten561_73
#print axioms coreCheck561_73
end Erdos883Verified
