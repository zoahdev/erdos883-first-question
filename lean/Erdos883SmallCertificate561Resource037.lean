import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_37 :
    (List.ofFn coreChunks561_37).flatten =
      (coreData561.take (coreResources561 37).q).drop 72 := by
  decide +kernel

theorem coreCheck561_37 :
    ∀ c : Fin 1, (coreChunks561_37 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 37)) = true := by
  decide +kernel
#print axioms coreFlatten561_37
#print axioms coreCheck561_37
end Erdos883Verified
