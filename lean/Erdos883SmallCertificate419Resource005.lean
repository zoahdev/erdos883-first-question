import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_5 :
    (List.ofFn coreChunks419_5).flatten =
      (coreData419.take (coreResources419 5).q).drop 56 := by
  decide +kernel

theorem coreCheck419_5 :
    ∀ c : Fin 2, (coreChunks419_5 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 5)) = true := by
  decide +kernel
#print axioms coreFlatten419_5
#print axioms coreCheck419_5
end Erdos883Verified
