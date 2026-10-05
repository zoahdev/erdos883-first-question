import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten35_3 :
    (List.ofFn coreChunks35_3).flatten =
      (coreData35.take (coreResources35 3).q).drop 8 := by
  decide +kernel

theorem coreCheck35_3 :
    ∀ c : Fin 1, (coreChunks35_3 c).all
      (coreResourceRowCheck 32 coreData35 (coreResources35 3)) = true := by
  decide +kernel
#print axioms coreFlatten35_3
#print axioms coreCheck35_3
end Erdos883Verified
