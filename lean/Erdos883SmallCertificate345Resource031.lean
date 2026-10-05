import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_31 :
    (List.ofFn coreChunks345_31).flatten =
      (coreData345.take (coreResources345 31).q).drop 62 := by
  decide +kernel

theorem coreCheck345_31 :
    ∀ c : Fin 1, (coreChunks345_31 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 31)) = true := by
  decide +kernel
#print axioms coreFlatten345_31
#print axioms coreCheck345_31
end Erdos883Verified
