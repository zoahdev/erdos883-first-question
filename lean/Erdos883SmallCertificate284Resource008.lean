import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_8 :
    (List.ofFn coreChunks284_8).flatten =
      (coreData284.take (coreResources284 8).q).drop 66 := by
  decide +kernel

theorem coreCheck284_8 :
    ∀ c : Fin 1, (coreChunks284_8 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 8)) = true := by
  decide +kernel
#print axioms coreFlatten284_8
#print axioms coreCheck284_8
end Erdos883Verified
