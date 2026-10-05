import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_83 :
    (List.ofFn coreChunks561_83).flatten =
      (coreData561.take (coreResources561 83).q).drop 157 := by
  decide +kernel

theorem coreCheck561_83 :
    ∀ c : Fin 1, (coreChunks561_83 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 83)) = true := by
  decide +kernel
#print axioms coreFlatten561_83
#print axioms coreCheck561_83
end Erdos883Verified
