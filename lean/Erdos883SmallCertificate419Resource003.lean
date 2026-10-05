import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_3 :
    (List.ofFn coreChunks419_3).flatten =
      (coreData419.take (coreResources419 3).q).drop 51 := by
  decide +kernel

theorem coreCheck419_3 :
    ∀ c : Fin 1, (coreChunks419_3 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 3)) = true := by
  decide +kernel
#print axioms coreFlatten419_3
#print axioms coreCheck419_3
end Erdos883Verified
