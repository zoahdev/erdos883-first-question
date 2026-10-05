import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_88 :
    (List.ofFn coreChunks561_88).flatten =
      (coreData561.take (coreResources561 88).q).drop 173 := by
  decide +kernel

theorem coreCheck561_88 :
    ∀ c : Fin 1, (coreChunks561_88 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 88)) = true := by
  decide +kernel
#print axioms coreFlatten561_88
#print axioms coreCheck561_88
end Erdos883Verified
