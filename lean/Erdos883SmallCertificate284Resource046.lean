import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_46 :
    (List.ofFn coreChunks284_46).flatten =
      (coreData284.take (coreResources284 46).q).drop 106 := by
  decide +kernel

theorem coreCheck284_46 :
    ∀ c : Fin 1, (coreChunks284_46 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 46)) = true := by
  decide +kernel
#print axioms coreFlatten284_46
#print axioms coreCheck284_46
end Erdos883Verified
