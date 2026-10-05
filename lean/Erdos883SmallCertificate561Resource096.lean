import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_96 :
    (List.ofFn coreChunks561_96).flatten =
      (coreData561.take (coreResources561 96).q).drop 232 := by
  decide +kernel

theorem coreCheck561_96 :
    ∀ c : Fin 1, (coreChunks561_96 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 96)) = true := by
  decide +kernel
#print axioms coreFlatten561_96
#print axioms coreCheck561_96
end Erdos883Verified
