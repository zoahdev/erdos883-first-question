import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_41 :
    (List.ofFn coreChunks284_41).flatten =
      (coreData284.take (coreResources284 41).q).drop 84 := by
  decide +kernel

theorem coreCheck284_41 :
    ∀ c : Fin 1, (coreChunks284_41 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 41)) = true := by
  decide +kernel
#print axioms coreFlatten284_41
#print axioms coreCheck284_41
end Erdos883Verified
