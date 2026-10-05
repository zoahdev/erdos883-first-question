import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_56 :
    (List.ofFn coreChunks345_56).flatten =
      (coreData345.take (coreResources345 56).q).drop 107 := by
  decide +kernel

theorem coreCheck345_56 :
    ∀ c : Fin 1, (coreChunks345_56 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 56)) = true := by
  decide +kernel
#print axioms coreFlatten345_56
#print axioms coreCheck345_56
end Erdos883Verified
