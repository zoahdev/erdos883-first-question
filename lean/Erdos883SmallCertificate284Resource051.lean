import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_51 :
    (List.ofFn coreChunks284_51).flatten =
      (coreData284.take (coreResources284 51).q).drop 0 := by
  decide +kernel

theorem coreCheck284_51 :
    ∀ c : Fin 7, (coreChunks284_51 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 51)) = true := by
  decide +kernel
#print axioms coreFlatten284_51
#print axioms coreCheck284_51
end Erdos883Verified
