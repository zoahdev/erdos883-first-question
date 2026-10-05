import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten35_6 :
    (List.ofFn coreChunks35_6).flatten =
      (coreData35.take (coreResources35 6).q).drop 12 := by
  decide +kernel

theorem coreCheck35_6 :
    ∀ c : Fin 1, (coreChunks35_6 c).all
      (coreResourceRowCheck 32 coreData35 (coreResources35 6)) = true := by
  decide +kernel
#print axioms coreFlatten35_6
#print axioms coreCheck35_6
end Erdos883Verified
