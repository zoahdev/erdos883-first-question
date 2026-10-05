import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_37 :
    (List.ofFn coreChunks345_37).flatten =
      (coreData345.take (coreResources345 37).q).drop 72 := by
  decide +kernel

theorem coreCheck345_37 :
    ∀ c : Fin 1, (coreChunks345_37 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 37)) = true := by
  decide +kernel
#print axioms coreFlatten345_37
#print axioms coreCheck345_37
end Erdos883Verified
