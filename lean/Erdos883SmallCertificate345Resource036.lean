import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_36 :
    (List.ofFn coreChunks345_36).flatten =
      (coreData345.take (coreResources345 36).q).drop 70 := by
  decide +kernel

theorem coreCheck345_36 :
    ∀ c : Fin 1, (coreChunks345_36 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 36)) = true := by
  decide +kernel
#print axioms coreFlatten345_36
#print axioms coreCheck345_36
end Erdos883Verified
