import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_57 :
    (List.ofFn coreChunks345_57).flatten =
      (coreData345.take (coreResources345 57).q).drop 108 := by
  decide +kernel

theorem coreCheck345_57 :
    ∀ c : Fin 1, (coreChunks345_57 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 57)) = true := by
  decide +kernel
#print axioms coreFlatten345_57
#print axioms coreCheck345_57
end Erdos883Verified
