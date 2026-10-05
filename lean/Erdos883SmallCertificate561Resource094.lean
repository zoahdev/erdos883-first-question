import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_94 :
    (List.ofFn coreChunks561_94).flatten =
      (coreData561.take (coreResources561 94).q).drop 214 := by
  decide +kernel

theorem coreCheck561_94 :
    ∀ c : Fin 1, (coreChunks561_94 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 94)) = true := by
  decide +kernel
#print axioms coreFlatten561_94
#print axioms coreCheck561_94
end Erdos883Verified
