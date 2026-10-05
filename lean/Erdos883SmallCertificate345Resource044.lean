import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_44 :
    (List.ofFn coreChunks345_44).flatten =
      (coreData345.take (coreResources345 44).q).drop 85 := by
  decide +kernel

theorem coreCheck345_44 :
    ∀ c : Fin 1, (coreChunks345_44 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 44)) = true := by
  decide +kernel
#print axioms coreFlatten345_44
#print axioms coreCheck345_44
end Erdos883Verified
