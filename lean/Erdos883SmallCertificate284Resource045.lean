import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_45 :
    (List.ofFn coreChunks284_45).flatten =
      (coreData284.take (coreResources284 45).q).drop 100 := by
  decide +kernel

theorem coreCheck284_45 :
    ∀ c : Fin 1, (coreChunks284_45 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 45)) = true := by
  decide +kernel
#print axioms coreFlatten284_45
#print axioms coreCheck284_45
end Erdos883Verified
