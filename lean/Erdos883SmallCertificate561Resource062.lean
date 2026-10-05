import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_62 :
    (List.ofFn coreChunks561_62).flatten =
      (coreData561.take (coreResources561 62).q).drop 117 := by
  decide +kernel

theorem coreCheck561_62 :
    ∀ c : Fin 1, (coreChunks561_62 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 62)) = true := by
  decide +kernel
#print axioms coreFlatten561_62
#print axioms coreCheck561_62
end Erdos883Verified
