import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_76 :
    (List.ofFn coreChunks561_76).flatten =
      (coreData561.take (coreResources561 76).q).drop 142 := by
  decide +kernel

theorem coreCheck561_76 :
    ∀ c : Fin 1, (coreChunks561_76 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 76)) = true := by
  decide +kernel
#print axioms coreFlatten561_76
#print axioms coreCheck561_76
end Erdos883Verified
