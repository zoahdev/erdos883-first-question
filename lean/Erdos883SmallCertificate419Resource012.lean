import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_12 :
    (List.ofFn coreChunks419_12).flatten =
      (coreData419.take (coreResources419 12).q).drop 88 := by
  decide +kernel

theorem coreCheck419_12 :
    ∀ c : Fin 1, (coreChunks419_12 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 12)) = true := by
  decide +kernel
#print axioms coreFlatten419_12
#print axioms coreCheck419_12
end Erdos883Verified
