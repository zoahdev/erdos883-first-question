import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_25 :
    (List.ofFn coreChunks419_25).flatten =
      (coreData419.take (coreResources419 25).q).drop 58 := by
  decide +kernel

theorem coreCheck419_25 :
    ∀ c : Fin 1, (coreChunks419_25 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 25)) = true := by
  decide +kernel
#print axioms coreFlatten419_25
#print axioms coreCheck419_25
end Erdos883Verified
