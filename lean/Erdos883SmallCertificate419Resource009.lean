import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_9 :
    (List.ofFn coreChunks419_9).flatten =
      (coreData419.take (coreResources419 9).q).drop 84 := by
  decide +kernel

theorem coreCheck419_9 :
    ∀ c : Fin 1, (coreChunks419_9 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 9)) = true := by
  decide +kernel
#print axioms coreFlatten419_9
#print axioms coreCheck419_9
end Erdos883Verified
