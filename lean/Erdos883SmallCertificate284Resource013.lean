import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_13 :
    (List.ofFn coreChunks284_13).flatten =
      (coreData284.take (coreResources284 13).q).drop 31 := by
  decide +kernel

theorem coreCheck284_13 :
    ∀ c : Fin 1, (coreChunks284_13 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 13)) = true := by
  decide +kernel
#print axioms coreFlatten284_13
#print axioms coreCheck284_13
end Erdos883Verified
