import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_5 :
    (List.ofFn coreChunks284_5).flatten =
      (coreData284.take (coreResources284 5).q).drop 62 := by
  decide +kernel

theorem coreCheck284_5 :
    ∀ c : Fin 1, (coreChunks284_5 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 5)) = true := by
  decide +kernel
#print axioms coreFlatten284_5
#print axioms coreCheck284_5
end Erdos883Verified
