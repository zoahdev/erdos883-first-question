import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten35_7 :
    (List.ofFn coreChunks35_7).flatten =
      (coreData35.take (coreResources35 7).q).drop 15 := by
  decide +kernel

theorem coreCheck35_7 :
    ∀ c : Fin 1, (coreChunks35_7 c).all
      (coreResourceRowCheck 32 coreData35 (coreResources35 7)) = true := by
  decide +kernel
#print axioms coreFlatten35_7
#print axioms coreCheck35_7
end Erdos883Verified
