import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_30 :
    (List.ofFn coreChunks561_30).flatten =
      (coreData561.take (coreResources561 30).q).drop 130 := by
  decide +kernel

theorem coreCheck561_30 :
    ∀ c : Fin 1, (coreChunks561_30 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 30)) = true := by
  decide +kernel
#print axioms coreFlatten561_30
#print axioms coreCheck561_30
end Erdos883Verified
