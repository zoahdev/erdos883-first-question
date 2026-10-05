import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_26 :
    (List.ofFn coreChunks419_26).flatten =
      (coreData419.take (coreResources419 26).q).drop 59 := by
  decide +kernel

theorem coreCheck419_26 :
    ∀ c : Fin 1, (coreChunks419_26 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 26)) = true := by
  decide +kernel
#print axioms coreFlatten419_26
#print axioms coreCheck419_26
end Erdos883Verified
