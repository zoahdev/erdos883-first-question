import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_66 :
    (List.ofFn coreChunks345_66).flatten =
      (coreData345.take (coreResources345 66).q).drop 0 := by
  decide +kernel

theorem coreCheck345_66 :
    ∀ c : Fin 9, (coreChunks345_66 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 66)) = true := by
  decide +kernel
#print axioms coreFlatten345_66
#print axioms coreCheck345_66
end Erdos883Verified
