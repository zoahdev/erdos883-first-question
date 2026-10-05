import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_20 :
    (List.ofFn coreChunks284_20).flatten =
      (coreData284.take (coreResources284 20).q).drop 52 := by
  decide +kernel

theorem coreCheck284_20 :
    ∀ c : Fin 1, (coreChunks284_20 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 20)) = true := by
  decide +kernel
#print axioms coreFlatten284_20
#print axioms coreCheck284_20
end Erdos883Verified
