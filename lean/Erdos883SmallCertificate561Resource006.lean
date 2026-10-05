import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_6 :
    (List.ofFn coreChunks561_6).flatten =
      (coreData561.take (coreResources561 6).q).drop 73 := by
  decide +kernel

theorem coreCheck561_6 :
    ∀ c : Fin 1, (coreChunks561_6 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 6)) = true := by
  decide +kernel
#print axioms coreFlatten561_6
#print axioms coreCheck561_6
end Erdos883Verified
