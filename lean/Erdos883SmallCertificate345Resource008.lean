import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_8 :
    (List.ofFn coreChunks345_8).flatten =
      (coreData345.take (coreResources345 8).q).drop 69 := by
  decide +kernel

theorem coreCheck345_8 :
    ∀ c : Fin 1, (coreChunks345_8 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 8)) = true := by
  decide +kernel
#print axioms coreFlatten345_8
#print axioms coreCheck345_8
end Erdos883Verified
