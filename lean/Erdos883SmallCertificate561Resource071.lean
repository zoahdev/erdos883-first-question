import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_71 :
    (List.ofFn coreChunks561_71).flatten =
      (coreData561.take (coreResources561 71).q).drop 130 := by
  decide +kernel

theorem coreCheck561_71 :
    ∀ c : Fin 1, (coreChunks561_71 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 71)) = true := by
  decide +kernel
#print axioms coreFlatten561_71
#print axioms coreCheck561_71
end Erdos883Verified
