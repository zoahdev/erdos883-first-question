import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_89 :
    (List.ofFn coreChunks561_89).flatten =
      (coreData561.take (coreResources561 89).q).drop 174 := by
  decide +kernel

theorem coreCheck561_89 :
    ∀ c : Fin 1, (coreChunks561_89 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 89)) = true := by
  decide +kernel
#print axioms coreFlatten561_89
#print axioms coreCheck561_89
end Erdos883Verified
