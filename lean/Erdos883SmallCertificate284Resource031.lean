import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_31 :
    (List.ofFn coreChunks284_31).flatten =
      (coreData284.take (coreResources284 31).q).drop 67 := by
  decide +kernel

theorem coreCheck284_31 :
    ∀ c : Fin 1, (coreChunks284_31 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 31)) = true := by
  decide +kernel
#print axioms coreFlatten284_31
#print axioms coreCheck284_31
end Erdos883Verified
