import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_34 :
    (List.ofFn coreChunks284_34).flatten =
      (coreData284.take (coreResources284 34).q).drop 71 := by
  decide +kernel

theorem coreCheck284_34 :
    ∀ c : Fin 1, (coreChunks284_34 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 34)) = true := by
  decide +kernel
#print axioms coreFlatten284_34
#print axioms coreCheck284_34
end Erdos883Verified
