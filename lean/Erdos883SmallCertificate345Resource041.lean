import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_41 :
    (List.ofFn coreChunks345_41).flatten =
      (coreData345.take (coreResources345 41).q).drop 80 := by
  decide +kernel

theorem coreCheck345_41 :
    ∀ c : Fin 1, (coreChunks345_41 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 41)) = true := by
  decide +kernel
#print axioms coreFlatten345_41
#print axioms coreCheck345_41
end Erdos883Verified
