import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_59 :
    (List.ofFn coreChunks345_59).flatten =
      (coreData345.take (coreResources345 59).q).drop 120 := by
  decide +kernel

theorem coreCheck345_59 :
    ∀ c : Fin 1, (coreChunks345_59 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 59)) = true := by
  decide +kernel
#print axioms coreFlatten345_59
#print axioms coreCheck345_59
end Erdos883Verified
