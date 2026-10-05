import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_46 :
    (List.ofFn coreChunks561_46).flatten =
      (coreData561.take (coreResources561 46).q).drop 91 := by
  decide +kernel

theorem coreCheck561_46 :
    ∀ c : Fin 1, (coreChunks561_46 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 46)) = true := by
  decide +kernel
#print axioms coreFlatten561_46
#print axioms coreCheck561_46
end Erdos883Verified
