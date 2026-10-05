import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_40 :
    (List.ofFn coreChunks345_40).flatten =
      (coreData345.take (coreResources345 40).q).drop 75 := by
  decide +kernel

theorem coreCheck345_40 :
    ∀ c : Fin 1, (coreChunks345_40 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 40)) = true := by
  decide +kernel
#print axioms coreFlatten345_40
#print axioms coreCheck345_40
end Erdos883Verified
