import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten35_4 :
    (List.ofFn coreChunks35_4).flatten =
      (coreData35.take (coreResources35 4).q).drop 9 := by
  decide +kernel

theorem coreCheck35_4 :
    ∀ c : Fin 1, (coreChunks35_4 c).all
      (coreResourceRowCheck 32 coreData35 (coreResources35 4)) = true := by
  decide +kernel
#print axioms coreFlatten35_4
#print axioms coreCheck35_4
end Erdos883Verified
