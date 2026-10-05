import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_51 :
    (List.ofFn coreChunks345_51).flatten =
      (coreData345.take (coreResources345 51).q).drop 98 := by
  decide +kernel

theorem coreCheck345_51 :
    ∀ c : Fin 1, (coreChunks345_51 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 51)) = true := by
  decide +kernel
#print axioms coreFlatten345_51
#print axioms coreCheck345_51
end Erdos883Verified
