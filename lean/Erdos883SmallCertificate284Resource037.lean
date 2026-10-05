import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_37 :
    (List.ofFn coreChunks284_37).flatten =
      (coreData284.take (coreResources284 37).q).drop 77 := by
  decide +kernel

theorem coreCheck284_37 :
    ∀ c : Fin 1, (coreChunks284_37 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 37)) = true := by
  decide +kernel
#print axioms coreFlatten284_37
#print axioms coreCheck284_37
end Erdos883Verified
