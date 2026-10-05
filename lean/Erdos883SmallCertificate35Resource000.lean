import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten35_0 :
    (List.ofFn coreChunks35_0).flatten =
      (coreData35.take (coreResources35 0).q).drop 0 := by
  decide +kernel

theorem coreCheck35_0 :
    ∀ c : Fin 1, (coreChunks35_0 c).all
      (coreResourceRowCheck 32 coreData35 (coreResources35 0)) = true := by
  decide +kernel
#print axioms coreFlatten35_0
#print axioms coreCheck35_0
end Erdos883Verified
