import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_47 :
    (List.ofFn coreChunks561_47).flatten =
      (coreData561.take (coreResources561 47).q).drop 92 := by
  decide +kernel

theorem coreCheck561_47 :
    ∀ c : Fin 1, (coreChunks561_47 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 47)) = true := by
  decide +kernel
#print axioms coreFlatten561_47
#print axioms coreCheck561_47
end Erdos883Verified
