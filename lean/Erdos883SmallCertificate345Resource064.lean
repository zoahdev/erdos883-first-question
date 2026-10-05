import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_64 :
    (List.ofFn coreChunks345_64).flatten =
      (coreData345.take (coreResources345 64).q).drop 152 := by
  decide +kernel

theorem coreCheck345_64 :
    ∀ c : Fin 1, (coreChunks345_64 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 64)) = true := by
  decide +kernel
#print axioms coreFlatten345_64
#print axioms coreCheck345_64
end Erdos883Verified
