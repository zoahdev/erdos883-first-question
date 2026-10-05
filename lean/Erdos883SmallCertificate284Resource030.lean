import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_30 :
    (List.ofFn coreChunks284_30).flatten =
      (coreData284.take (coreResources284 30).q).drop 64 := by
  decide +kernel

theorem coreCheck284_30 :
    ∀ c : Fin 1, (coreChunks284_30 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 30)) = true := by
  decide +kernel
#print axioms coreFlatten284_30
#print axioms coreCheck284_30
end Erdos883Verified
