import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten35_1 :
    (List.ofFn coreChunks35_1).flatten =
      (coreData35.take (coreResources35 1).q).drop 6 := by
  decide +kernel

theorem coreCheck35_1 :
    ∀ c : Fin 1, (coreChunks35_1 c).all
      (coreResourceRowCheck 32 coreData35 (coreResources35 1)) = true := by
  decide +kernel
#print axioms coreFlatten35_1
#print axioms coreCheck35_1
end Erdos883Verified
