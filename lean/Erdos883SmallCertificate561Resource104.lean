import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_104 :
    (List.ofFn coreChunks561_104).flatten =
      (coreData561.take (coreResources561 104).q).drop 182 := by
  decide +kernel

theorem coreCheck561_104 :
    ∀ c : Fin 1, (coreChunks561_104 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 104)) = true := by
  decide +kernel
#print axioms coreFlatten561_104
#print axioms coreCheck561_104
end Erdos883Verified
