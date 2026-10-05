import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_7 :
    (List.ofFn coreChunks345_7).flatten =
      (coreData345.take (coreResources345 7).q).drop 68 := by
  decide +kernel

theorem coreCheck345_7 :
    ∀ c : Fin 1, (coreChunks345_7 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 7)) = true := by
  decide +kernel
#print axioms coreFlatten345_7
#print axioms coreCheck345_7
end Erdos883Verified
