import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_13 :
    (List.ofFn coreChunks419_13).flatten =
      (coreData419.take (coreResources419 13).q).drop 90 := by
  decide +kernel

theorem coreCheck419_13 :
    ∀ c : Fin 1, (coreChunks419_13 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 13)) = true := by
  decide +kernel
#print axioms coreFlatten419_13
#print axioms coreCheck419_13
end Erdos883Verified
