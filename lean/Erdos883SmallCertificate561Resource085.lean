import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_85 :
    (List.ofFn coreChunks561_85).flatten =
      (coreData561.take (coreResources561 85).q).drop 167 := by
  decide +kernel

theorem coreCheck561_85 :
    ∀ c : Fin 1, (coreChunks561_85 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 85)) = true := by
  decide +kernel
#print axioms coreFlatten561_85
#print axioms coreCheck561_85
end Erdos883Verified
