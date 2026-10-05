import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_39 :
    (List.ofFn coreChunks419_39).flatten =
      (coreData419.take (coreResources419 39).q).drop 82 := by
  decide +kernel

theorem coreCheck419_39 :
    ∀ c : Fin 1, (coreChunks419_39 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 39)) = true := by
  decide +kernel
#print axioms coreFlatten419_39
#print axioms coreCheck419_39
end Erdos883Verified
