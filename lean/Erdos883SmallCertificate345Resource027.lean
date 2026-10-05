import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_27 :
    (List.ofFn coreChunks345_27).flatten =
      (coreData345.take (coreResources345 27).q).drop 58 := by
  decide +kernel

theorem coreCheck345_27 :
    ∀ c : Fin 1, (coreChunks345_27 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 27)) = true := by
  decide +kernel
#print axioms coreFlatten345_27
#print axioms coreCheck345_27
end Erdos883Verified
