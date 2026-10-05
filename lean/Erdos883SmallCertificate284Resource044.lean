import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_44 :
    (List.ofFn coreChunks284_44).flatten =
      (coreData284.take (coreResources284 44).q).drop 95 := by
  decide +kernel

theorem coreCheck284_44 :
    ∀ c : Fin 1, (coreChunks284_44 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 44)) = true := by
  decide +kernel
#print axioms coreFlatten284_44
#print axioms coreCheck284_44
end Erdos883Verified
