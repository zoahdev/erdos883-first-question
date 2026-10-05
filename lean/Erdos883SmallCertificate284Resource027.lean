import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_27 :
    (List.ofFn coreChunks284_27).flatten =
      (coreData284.take (coreResources284 27).q).drop 61 := by
  decide +kernel

theorem coreCheck284_27 :
    ∀ c : Fin 1, (coreChunks284_27 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 27)) = true := by
  decide +kernel
#print axioms coreFlatten284_27
#print axioms coreCheck284_27
end Erdos883Verified
