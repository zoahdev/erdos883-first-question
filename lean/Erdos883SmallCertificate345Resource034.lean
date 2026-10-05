import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_34 :
    (List.ofFn coreChunks345_34).flatten =
      (coreData345.take (coreResources345 34).q).drop 68 := by
  decide +kernel

theorem coreCheck345_34 :
    ∀ c : Fin 1, (coreChunks345_34 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 34)) = true := by
  decide +kernel
#print axioms coreFlatten345_34
#print axioms coreCheck345_34
end Erdos883Verified
