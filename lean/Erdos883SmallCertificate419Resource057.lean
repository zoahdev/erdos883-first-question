import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_57 :
    (List.ofFn coreChunks419_57).flatten =
      (coreData419.take (coreResources419 57).q).drop 113 := by
  decide +kernel

theorem coreCheck419_57 :
    ∀ c : Fin 1, (coreChunks419_57 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 57)) = true := by
  decide +kernel
#print axioms coreFlatten419_57
#print axioms coreCheck419_57
end Erdos883Verified
