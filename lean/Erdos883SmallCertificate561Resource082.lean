import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_82 :
    (List.ofFn coreChunks561_82).flatten =
      (coreData561.take (coreResources561 82).q).drop 155 := by
  decide +kernel

theorem coreCheck561_82 :
    ∀ c : Fin 1, (coreChunks561_82 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 82)) = true := by
  decide +kernel
#print axioms coreFlatten561_82
#print axioms coreCheck561_82
end Erdos883Verified
