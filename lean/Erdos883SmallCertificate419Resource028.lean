import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_28 :
    (List.ofFn coreChunks419_28).flatten =
      (coreData419.take (coreResources419 28).q).drop 65 := by
  decide +kernel

theorem coreCheck419_28 :
    ∀ c : Fin 1, (coreChunks419_28 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 28)) = true := by
  decide +kernel
#print axioms coreFlatten419_28
#print axioms coreCheck419_28
end Erdos883Verified
