import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_65 :
    (List.ofFn coreChunks345_65).flatten =
      (coreData345.take (coreResources345 65).q).drop 164 := by
  decide +kernel

theorem coreCheck345_65 :
    ∀ c : Fin 1, (coreChunks345_65 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 65)) = true := by
  decide +kernel
#print axioms coreFlatten345_65
#print axioms coreCheck345_65
end Erdos883Verified
