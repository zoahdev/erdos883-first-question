import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_35 :
    (List.ofFn coreChunks284_35).flatten =
      (coreData284.take (coreResources284 35).q).drop 72 := by
  decide +kernel

theorem coreCheck284_35 :
    ∀ c : Fin 1, (coreChunks284_35 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 35)) = true := by
  decide +kernel
#print axioms coreFlatten284_35
#print axioms coreCheck284_35
end Erdos883Verified
