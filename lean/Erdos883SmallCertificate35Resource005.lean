import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten35_5 :
    (List.ofFn coreChunks35_5).flatten =
      (coreData35.take (coreResources35 5).q).drop 11 := by
  decide +kernel

theorem coreCheck35_5 :
    ∀ c : Fin 1, (coreChunks35_5 c).all
      (coreResourceRowCheck 32 coreData35 (coreResources35 5)) = true := by
  decide +kernel
#print axioms coreFlatten35_5
#print axioms coreCheck35_5
end Erdos883Verified
