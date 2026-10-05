import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_38 :
    (List.ofFn coreChunks345_38).flatten =
      (coreData345.take (coreResources345 38).q).drop 73 := by
  decide +kernel

theorem coreCheck345_38 :
    ∀ c : Fin 1, (coreChunks345_38 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 38)) = true := by
  decide +kernel
#print axioms coreFlatten345_38
#print axioms coreCheck345_38
end Erdos883Verified
