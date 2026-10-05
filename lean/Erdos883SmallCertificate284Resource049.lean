import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_49 :
    (List.ofFn coreChunks284_49).flatten =
      (coreData284.take (coreResources284 49).q).drop 125 := by
  decide +kernel

theorem coreCheck284_49 :
    ∀ c : Fin 1, (coreChunks284_49 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 49)) = true := by
  decide +kernel
#print axioms coreFlatten284_49
#print axioms coreCheck284_49
end Erdos883Verified
