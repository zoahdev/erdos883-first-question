import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_29 :
    (List.ofFn coreChunks419_29).flatten =
      (coreData419.take (coreResources419 29).q).drop 67 := by
  decide +kernel

theorem coreCheck419_29 :
    ∀ c : Fin 1, (coreChunks419_29 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 29)) = true := by
  decide +kernel
#print axioms coreFlatten419_29
#print axioms coreCheck419_29
end Erdos883Verified
