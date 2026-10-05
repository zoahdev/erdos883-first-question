import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_46 :
    (List.ofFn coreChunks345_46).flatten =
      (coreData345.take (coreResources345 46).q).drop 88 := by
  decide +kernel

theorem coreCheck345_46 :
    ∀ c : Fin 1, (coreChunks345_46 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 46)) = true := by
  decide +kernel
#print axioms coreFlatten345_46
#print axioms coreCheck345_46
end Erdos883Verified
