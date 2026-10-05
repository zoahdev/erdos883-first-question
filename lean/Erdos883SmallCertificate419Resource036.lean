import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_36 :
    (List.ofFn coreChunks419_36).flatten =
      (coreData419.take (coreResources419 36).q).drop 76 := by
  decide +kernel

theorem coreCheck419_36 :
    ∀ c : Fin 1, (coreChunks419_36 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 36)) = true := by
  decide +kernel
#print axioms coreFlatten419_36
#print axioms coreCheck419_36
end Erdos883Verified
