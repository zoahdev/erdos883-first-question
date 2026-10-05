import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten35_8 :
    (List.ofFn coreChunks35_8).flatten =
      (coreData35.take (coreResources35 8).q).drop 0 := by
  decide +kernel

theorem coreCheck35_8 :
    ∀ c : Fin 1, (coreChunks35_8 c).all
      (coreResourceRowCheck 32 coreData35 (coreResources35 8)) = true := by
  decide +kernel
#print axioms coreFlatten35_8
#print axioms coreCheck35_8
end Erdos883Verified
