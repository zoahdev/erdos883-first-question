import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_75 :
    (List.ofFn coreChunks419_75).flatten =
      (coreData419.take (coreResources419 75).q).drop 0 := by
  decide +kernel

theorem coreCheck419_75 :
    ∀ c : Fin 9, (coreChunks419_75 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 75)) = true := by
  decide +kernel
#print axioms coreFlatten419_75
#print axioms coreCheck419_75
end Erdos883Verified
