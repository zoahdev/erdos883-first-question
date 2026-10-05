import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_35 :
    (List.ofFn coreChunks419_35).flatten =
      (coreData419.take (coreResources419 35).q).drop 74 := by
  decide +kernel

theorem coreCheck419_35 :
    ∀ c : Fin 1, (coreChunks419_35 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 35)) = true := by
  decide +kernel
#print axioms coreFlatten419_35
#print axioms coreCheck419_35
end Erdos883Verified
