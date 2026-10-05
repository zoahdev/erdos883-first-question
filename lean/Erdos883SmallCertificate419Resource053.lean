import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_53 :
    (List.ofFn coreChunks419_53).flatten =
      (coreData419.take (coreResources419 53).q).drop 105 := by
  decide +kernel

theorem coreCheck419_53 :
    ∀ c : Fin 1, (coreChunks419_53 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 53)) = true := by
  decide +kernel
#print axioms coreFlatten419_53
#print axioms coreCheck419_53
end Erdos883Verified
