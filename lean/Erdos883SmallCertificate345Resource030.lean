import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_30 :
    (List.ofFn coreChunks345_30).flatten =
      (coreData345.take (coreResources345 30).q).drop 61 := by
  decide +kernel

theorem coreCheck345_30 :
    ∀ c : Fin 1, (coreChunks345_30 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 30)) = true := by
  decide +kernel
#print axioms coreFlatten345_30
#print axioms coreCheck345_30
end Erdos883Verified
