import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_18 :
    (List.ofFn coreChunks419_18).flatten =
      (coreData419.take (coreResources419 18).q).drop 98 := by
  decide +kernel

theorem coreCheck419_18 :
    ∀ c : Fin 1, (coreChunks419_18 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 18)) = true := by
  decide +kernel
#print axioms coreFlatten419_18
#print axioms coreCheck419_18
end Erdos883Verified
