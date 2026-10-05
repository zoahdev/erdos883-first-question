import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_86 :
    (List.ofFn coreChunks561_86).flatten =
      (coreData561.take (coreResources561 86).q).drop 168 := by
  decide +kernel

theorem coreCheck561_86 :
    ∀ c : Fin 1, (coreChunks561_86 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 86)) = true := by
  decide +kernel
#print axioms coreFlatten561_86
#print axioms coreCheck561_86
end Erdos883Verified
