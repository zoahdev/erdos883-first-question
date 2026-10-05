import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_49 :
    (List.ofFn coreChunks419_49).flatten =
      (coreData419.take (coreResources419 49).q).drop 98 := by
  decide +kernel

theorem coreCheck419_49 :
    ∀ c : Fin 1, (coreChunks419_49 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 49)) = true := by
  decide +kernel
#print axioms coreFlatten419_49
#print axioms coreCheck419_49
end Erdos883Verified
