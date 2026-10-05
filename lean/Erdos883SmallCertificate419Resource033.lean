import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_33 :
    (List.ofFn coreChunks419_33).flatten =
      (coreData419.take (coreResources419 33).q).drop 72 := by
  decide +kernel

theorem coreCheck419_33 :
    ∀ c : Fin 1, (coreChunks419_33 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 33)) = true := by
  decide +kernel
#print axioms coreFlatten419_33
#print axioms coreCheck419_33
end Erdos883Verified
