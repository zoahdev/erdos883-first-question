import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_47 :
    (List.ofFn coreChunks284_47).flatten =
      (coreData284.take (coreResources284 47).q).drop 113 := by
  decide +kernel

theorem coreCheck284_47 :
    ∀ c : Fin 1, (coreChunks284_47 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 47)) = true := by
  decide +kernel
#print axioms coreFlatten284_47
#print axioms coreCheck284_47
end Erdos883Verified
