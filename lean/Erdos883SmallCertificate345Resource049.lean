import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_49 :
    (List.ofFn coreChunks345_49).flatten =
      (coreData345.take (coreResources345 49).q).drop 93 := by
  decide +kernel

theorem coreCheck345_49 :
    ∀ c : Fin 1, (coreChunks345_49 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 49)) = true := by
  decide +kernel
#print axioms coreFlatten345_49
#print axioms coreCheck345_49
end Erdos883Verified
