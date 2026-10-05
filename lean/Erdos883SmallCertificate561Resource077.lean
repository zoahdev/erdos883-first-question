import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_77 :
    (List.ofFn coreChunks561_77).flatten =
      (coreData561.take (coreResources561 77).q).drop 144 := by
  decide +kernel

theorem coreCheck561_77 :
    ∀ c : Fin 1, (coreChunks561_77 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 77)) = true := by
  decide +kernel
#print axioms coreFlatten561_77
#print axioms coreCheck561_77
end Erdos883Verified
