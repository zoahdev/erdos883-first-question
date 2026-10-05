import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_32 :
    (List.ofFn coreChunks284_32).flatten =
      (coreData284.take (coreResources284 32).q).drop 68 := by
  decide +kernel

theorem coreCheck284_32 :
    ∀ c : Fin 1, (coreChunks284_32 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 32)) = true := by
  decide +kernel
#print axioms coreFlatten284_32
#print axioms coreCheck284_32
end Erdos883Verified
