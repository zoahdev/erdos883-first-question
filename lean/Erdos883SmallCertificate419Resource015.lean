import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_15 :
    (List.ofFn coreChunks419_15).flatten =
      (coreData419.take (coreResources419 15).q).drop 92 := by
  decide +kernel

theorem coreCheck419_15 :
    ∀ c : Fin 1, (coreChunks419_15 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 15)) = true := by
  decide +kernel
#print axioms coreFlatten419_15
#print axioms coreCheck419_15
end Erdos883Verified
