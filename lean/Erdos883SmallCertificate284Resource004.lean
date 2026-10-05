import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_4 :
    (List.ofFn coreChunks284_4).flatten =
      (coreData284.take (coreResources284 4).q).drop 61 := by
  decide +kernel

theorem coreCheck284_4 :
    ∀ c : Fin 1, (coreChunks284_4 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 4)) = true := by
  decide +kernel
#print axioms coreFlatten284_4
#print axioms coreCheck284_4
end Erdos883Verified
