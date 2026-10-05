import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_23 :
    (List.ofFn coreChunks419_23).flatten =
      (coreData419.take (coreResources419 23).q).drop 105 := by
  decide +kernel

theorem coreCheck419_23 :
    ∀ c : Fin 1, (coreChunks419_23 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 23)) = true := by
  decide +kernel
#print axioms coreFlatten419_23
#print axioms coreCheck419_23
end Erdos883Verified
