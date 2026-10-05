import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_52 :
    (List.ofFn coreChunks345_52).flatten =
      (coreData345.take (coreResources345 52).q).drop 101 := by
  decide +kernel

theorem coreCheck345_52 :
    ∀ c : Fin 1, (coreChunks345_52 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 52)) = true := by
  decide +kernel
#print axioms coreFlatten345_52
#print axioms coreCheck345_52
end Erdos883Verified
