import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_29 :
    (List.ofFn coreChunks345_29).flatten =
      (coreData345.take (coreResources345 29).q).drop 60 := by
  decide +kernel

theorem coreCheck345_29 :
    ∀ c : Fin 1, (coreChunks345_29 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 29)) = true := by
  decide +kernel
#print axioms coreFlatten345_29
#print axioms coreCheck345_29
end Erdos883Verified
