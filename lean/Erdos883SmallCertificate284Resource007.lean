import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_7 :
    (List.ofFn coreChunks284_7).flatten =
      (coreData284.take (coreResources284 7).q).drop 64 := by
  decide +kernel

theorem coreCheck284_7 :
    ∀ c : Fin 1, (coreChunks284_7 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 7)) = true := by
  decide +kernel
#print axioms coreFlatten284_7
#print axioms coreCheck284_7
end Erdos883Verified
