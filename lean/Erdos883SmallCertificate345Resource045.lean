import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_45 :
    (List.ofFn coreChunks345_45).flatten =
      (coreData345.take (coreResources345 45).q).drop 87 := by
  decide +kernel

theorem coreCheck345_45 :
    ∀ c : Fin 1, (coreChunks345_45 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 45)) = true := by
  decide +kernel
#print axioms coreFlatten345_45
#print axioms coreCheck345_45
end Erdos883Verified
