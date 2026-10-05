import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_2 :
    (List.ofFn coreChunks345_2).flatten =
      (coreData345.take (coreResources345 2).q).drop 33 := by
  decide +kernel

theorem coreCheck345_2 :
    ∀ c : Fin 1, (coreChunks345_2 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 2)) = true := by
  decide +kernel
#print axioms coreFlatten345_2
#print axioms coreCheck345_2
end Erdos883Verified
