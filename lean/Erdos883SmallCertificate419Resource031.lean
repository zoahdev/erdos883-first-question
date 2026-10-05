import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_31 :
    (List.ofFn coreChunks419_31).flatten =
      (coreData419.take (coreResources419 31).q).drop 70 := by
  decide +kernel

theorem coreCheck419_31 :
    ∀ c : Fin 1, (coreChunks419_31 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 31)) = true := by
  decide +kernel
#print axioms coreFlatten419_31
#print axioms coreCheck419_31
end Erdos883Verified
