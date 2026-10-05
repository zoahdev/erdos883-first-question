import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_69 :
    (List.ofFn coreChunks345_69).flatten =
      (coreData345.take (coreResources345 69).q).drop 0 := by
  decide +kernel

theorem coreCheck345_69 :
    ∀ c : Fin 6, (coreChunks345_69 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 69)) = true := by
  decide +kernel
#print axioms coreFlatten345_69
#print axioms coreCheck345_69
end Erdos883Verified
