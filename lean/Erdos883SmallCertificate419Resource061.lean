import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_61 :
    (List.ofFn coreChunks419_61).flatten =
      (coreData419.take (coreResources419 61).q).drop 125 := by
  decide +kernel

theorem coreCheck419_61 :
    ∀ c : Fin 1, (coreChunks419_61 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 61)) = true := by
  decide +kernel
#print axioms coreFlatten419_61
#print axioms coreCheck419_61
end Erdos883Verified
