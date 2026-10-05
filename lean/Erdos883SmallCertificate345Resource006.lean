import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_6 :
    (List.ofFn coreChunks345_6).flatten =
      (coreData345.take (coreResources345 6).q).drop 65 := by
  decide +kernel

theorem coreCheck345_6 :
    ∀ c : Fin 1, (coreChunks345_6 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 6)) = true := by
  decide +kernel
#print axioms coreFlatten345_6
#print axioms coreCheck345_6
end Erdos883Verified
