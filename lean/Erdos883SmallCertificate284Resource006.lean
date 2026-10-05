import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_6 :
    (List.ofFn coreChunks284_6).flatten =
      (coreData284.take (coreResources284 6).q).drop 63 := by
  decide +kernel

theorem coreCheck284_6 :
    ∀ c : Fin 1, (coreChunks284_6 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 6)) = true := by
  decide +kernel
#print axioms coreFlatten284_6
#print axioms coreCheck284_6
end Erdos883Verified
