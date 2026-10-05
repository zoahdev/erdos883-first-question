import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_42 :
    (List.ofFn coreChunks419_42).flatten =
      (coreData419.take (coreResources419 42).q).drop 86 := by
  decide +kernel

theorem coreCheck419_42 :
    ∀ c : Fin 1, (coreChunks419_42 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 42)) = true := by
  decide +kernel
#print axioms coreFlatten419_42
#print axioms coreCheck419_42
end Erdos883Verified
