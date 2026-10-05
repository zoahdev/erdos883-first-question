import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_55 :
    (List.ofFn coreChunks284_55).flatten =
      (coreData284.take (coreResources284 55).q).drop 0 := by
  decide +kernel

theorem coreCheck284_55 :
    ∀ c : Fin 6, (coreChunks284_55 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 55)) = true := by
  decide +kernel
#print axioms coreFlatten284_55
#print axioms coreCheck284_55
end Erdos883Verified
