import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_92 :
    (List.ofFn coreChunks561_92).flatten =
      (coreData561.take (coreResources561 92).q).drop 190 := by
  decide +kernel

theorem coreCheck561_92 :
    ∀ c : Fin 1, (coreChunks561_92 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 92)) = true := by
  decide +kernel
#print axioms coreFlatten561_92
#print axioms coreCheck561_92
end Erdos883Verified
