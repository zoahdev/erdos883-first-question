import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_40 :
    (List.ofFn coreChunks284_40).flatten =
      (coreData284.take (coreResources284 40).q).drop 82 := by
  decide +kernel

theorem coreCheck284_40 :
    ∀ c : Fin 1, (coreChunks284_40 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 40)) = true := by
  decide +kernel
#print axioms coreFlatten284_40
#print axioms coreCheck284_40
end Erdos883Verified
