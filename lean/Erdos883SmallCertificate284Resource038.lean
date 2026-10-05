import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_38 :
    (List.ofFn coreChunks284_38).flatten =
      (coreData284.take (coreResources284 38).q).drop 78 := by
  decide +kernel

theorem coreCheck284_38 :
    ∀ c : Fin 1, (coreChunks284_38 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 38)) = true := by
  decide +kernel
#print axioms coreFlatten284_38
#print axioms coreCheck284_38
end Erdos883Verified
