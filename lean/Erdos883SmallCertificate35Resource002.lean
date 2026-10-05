import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten35_2 :
    (List.ofFn coreChunks35_2).flatten =
      (coreData35.take (coreResources35 2).q).drop 7 := by
  decide +kernel

theorem coreCheck35_2 :
    ∀ c : Fin 1, (coreChunks35_2 c).all
      (coreResourceRowCheck 32 coreData35 (coreResources35 2)) = true := by
  decide +kernel
#print axioms coreFlatten35_2
#print axioms coreCheck35_2
end Erdos883Verified
